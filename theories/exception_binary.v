(** A verified, list-based decoder for the final EH catch immediates.

    This is not yet connected to the module parser or extraction. The existing
    Parseque parser and LEB128 printer have separate, undischarged correctness
    obligations; importing their printer below does not assume its correctness.
    The relation [unsigned32] describes bounded unsigned LEB128, including
    permitted non-minimal encodings and the restricted fifth byte. *)
From Stdlib Require Import List NArith Init.Byte Lia.
From Wasm Require Import datatypes exception_handling leb128.
Import ListNotations.

Module EHBinary.
Import EH.

(** Exception-only fragment of Babsheaptype/Breftype, pinned to
    WebAssembly/spec 04931610158e1ae1c69a3abf49e73984c0d4ddaf,
    specification/wasm-3.0/5.2-binary.types.spectec.
    These are NOT generic heap/reference parsers. *)
Definition binary_of_exception_heap (h : exception_heap_type) : Byte.byte :=
  match h with HT_exn => x69 | HT_noexn => x74 end.

Definition read_exception_heap (bs : list Byte.byte)
    : option (exception_heap_type * list Byte.byte) :=
  match bs with
  | x69 :: rest => Some (HT_exn, rest)
  | x74 :: rest => Some (HT_noexn, rest)
  | _ => None
  end.

Lemma read_exception_heap_spec bs h rest :
  read_exception_heap bs = Some (h, rest) <->
  bs = binary_of_exception_heap h :: rest.
Proof.
  split.
  - destruct bs as [|b tail]; [discriminate|].
    destruct b; simpl; intro H; try discriminate;
      inversion H; subst; reflexivity.
  - intro H; subst; destruct h; reflexivity.
Qed.

Definition read_reference_body (nullable : bool) (bs : list Byte.byte)
    : option (exception_reference_type * list Byte.byte) :=
  match read_exception_heap bs with
  | Some (h, rest) =>
      Some ({| exception_nullable := nullable; exception_heap := h |}, rest)
  | None => None
  end.

Definition read_exception_reference (bs : list Byte.byte)
    : option (exception_reference_type * list Byte.byte) :=
  match bs with
  | x63 :: tail => read_reference_body true tail
  | x64 :: tail => read_reference_body false tail
  | x69 :: tail =>
      Some ({| exception_nullable := true; exception_heap := HT_exn |}, tail)
  | x74 :: tail =>
      Some ({| exception_nullable := true; exception_heap := HT_noexn |}, tail)
  | _ => None
  end.

Inductive exception_reference_binary :
    list Byte.byte -> exception_reference_type -> list Byte.byte -> Prop :=
| Binary_reference_explicit (nullable : bool) h rest :
    exception_reference_binary
      ((if nullable then x63 else x64) :: binary_of_exception_heap h :: rest)
      {| exception_nullable := nullable; exception_heap := h |} rest
| Binary_reference_short h rest :
    exception_reference_binary (binary_of_exception_heap h :: rest)
      {| exception_nullable := true; exception_heap := h |} rest.

Lemma read_reference_body_spec nullable bs t rest :
  read_reference_body nullable bs = Some (t, rest) <->
  exists h, bs = binary_of_exception_heap h :: rest /\
    t = {| exception_nullable := nullable; exception_heap := h |}.
Proof.
  unfold read_reference_body; split.
  - destruct (read_exception_heap bs) as [[h tail]|] eqn:Hh; [|discriminate].
    intro H; inversion H; subst; exists h; split; [|reflexivity].
    apply read_exception_heap_spec; assumption.
  - intros [h [Hbs Ht]]; subst.
    destruct h; reflexivity.
Qed.

Theorem read_exception_reference_correct bs t rest :
  read_exception_reference bs = Some (t, rest) <->
  exception_reference_binary bs t rest.
Proof.
  split.
  - destruct bs as [|b tail]; [discriminate|].
    destruct b; simpl; try discriminate.
    + rewrite read_reference_body_spec.
      intros [h [Hbs Ht]]; subst.
      exact (Binary_reference_explicit true h rest).
    + rewrite read_reference_body_spec.
      intros [h [Hbs Ht]]; subst.
      exact (Binary_reference_explicit false h rest).
    + intro H; inversion H; subst; apply (Binary_reference_short HT_exn).
    + intro H; inversion H; subst; apply (Binary_reference_short HT_noexn).
  - intro H; destruct H.
    + destruct nullable, h; reflexivity.
    + destruct h; reflexivity.
Qed.

Definition binary_of_exception_reference (t : exception_reference_type)
    : list Byte.byte :=
  [if t.(exception_nullable) then x63 else x64;
   binary_of_exception_heap t.(exception_heap)].

Theorem exception_reference_roundtrip t rest :
  read_exception_reference (binary_of_exception_reference t ++ rest) =
  Some (t, rest).
Proof.
  destruct t as [nullable h]; destruct nullable, h; reflexivity.
Qed.

Definition final_bound (remaining : nat) : N :=
  match remaining with
  | O => 16
  | S _ => 128
  end%N.

Fixpoint read_unsigned32 (fuel : nat) (bs : list Byte.byte)
    : option (N * list Byte.byte) :=
  match fuel, bs with
  | S remaining, b :: tail =>
      let n := Byte.to_N b in
      if N.ltb n 128 then
        if N.ltb n (final_bound remaining) then Some (n, tail) else None
      else
        match remaining with
        | O => None
        | S _ =>
            match read_unsigned32 remaining tail with
            | Some (high, rest) => Some ((n - 128 + 128 * high)%N, rest)
            | None => None
            end
        end
  | _, _ => None
  end.

Definition read_u32 := read_unsigned32 5.

Inductive unsigned32 : nat -> list Byte.byte -> N -> list Byte.byte -> Prop :=
| Unsigned_end remaining b tail :
    (Byte.to_N b < 128)%N ->
    (Byte.to_N b < final_bound remaining)%N ->
    unsigned32 (S remaining) (b :: tail) (Byte.to_N b) tail
| Unsigned_more remaining b tail high rest :
    (128 <= Byte.to_N b)%N ->
    unsigned32 (S remaining) tail high rest ->
    unsigned32 (S (S remaining)) (b :: tail)
      (Byte.to_N b - 128 + 128 * high)%N rest.

Theorem read_unsigned32_correct fuel bs n rest :
  read_unsigned32 fuel bs = Some (n, rest) <->
  unsigned32 fuel bs n rest.
Proof.
  split.
  - revert bs n rest; induction fuel as [|remaining IH];
      intros bs n rest H; simpl in H; [discriminate|].
    destruct bs as [|b tail]; [discriminate|].
    destruct (N.ltb (Byte.to_N b) 128) eqn:Hcont.
    + destruct (N.ltb (Byte.to_N b) (final_bound remaining)) eqn:Hbound;
        try discriminate.
      inversion H; subst; constructor; apply N.ltb_lt; assumption.
    + destruct remaining as [|remaining]; [discriminate|].
      destruct (read_unsigned32 (S remaining) tail)
        as [[high rest']|] eqn:Hr; [|discriminate].
      inversion H; subst; constructor.
      * apply N.ltb_ge; assumption.
      * apply IH; assumption.
  - intro H; induction H; simpl.
    + apply N.ltb_lt in H; apply N.ltb_lt in H0.
      rewrite H, H0; reflexivity.
    + apply N.ltb_ge in H; rewrite H.
      change
        (match read_unsigned32 (S remaining) tail with
         | Some (high', rest') =>
             Some ((Byte.to_N b - 128 + 128 * high')%N, rest')
         | None => None
         end = Some ((Byte.to_N b - 128 + 128 * high)%N, rest)).
      rewrite IHunsigned32; reflexivity.
Qed.

Corollary read_u32_correct bs n rest :
  read_u32 bs = Some (n, rest) <-> unsigned32 5 bs n rest.
Proof. apply read_unsigned32_correct. Qed.

Fixpoint unsigned_limit (fuel : nat) : N :=
  match fuel with
  | O => 0
  | S remaining =>
      match remaining with
      | O => 16
      | S _ => 128 * unsigned_limit remaining
      end
  end%N.

Lemma unsigned_limit_positive remaining :
  (16 <= unsigned_limit (S remaining))%N.
Proof.
  induction remaining as [|remaining IH]; [reflexivity|].
  change (16 <= 128 * unsigned_limit (S remaining))%N; nia.
Qed.

Lemma byte_bound (b : Byte.byte) : (Byte.to_N b < 256)%N.
Proof. destruct b; reflexivity. Qed.

Lemma unsigned32_bound fuel bs n rest :
  unsigned32 fuel bs n rest -> (n < unsigned_limit fuel)%N.
Proof.
  intro H; induction H.
  - destruct remaining as [|remaining]; [exact H0|].
    change (Byte.to_N b < 128 * unsigned_limit (S remaining))%N.
    pose proof (unsigned_limit_positive remaining); nia.
  - change (Byte.to_N b - 128 + 128 * high <
            128 * unsigned_limit (S remaining))%N.
    pose proof (byte_bound b); nia.
Qed.

Corollary read_u32_bounded bs n rest :
  read_u32 bs = Some (n, rest) -> (n < 4294967296)%N.
Proof.
  intro H; apply read_u32_correct in H.
  exact (unsigned32_bound 5 bs n rest H).
Qed.

(** Every successful decode consumes bytes, never fabricates a remainder. *)
Lemma unsigned32_suffix fuel bs n rest :
  unsigned32 fuel bs n rest ->
  exists consumed, consumed <> [] /\ bs = consumed ++ rest /\
                   (length consumed <= fuel)%nat.
Proof.
  intro H; induction H.
  - exists [b]; simpl; repeat split; try discriminate; auto with arith.
  - destruct IHunsigned32 as [prefix [Hne [Heq Hlen]]].
    exists (b :: prefix); simpl; repeat split; try discriminate.
    + rewrite Heq; reflexivity.
    + auto with arith.
Qed.

Definition read_tagged_catch (make : tagidx -> labelidx -> catch_clause)
    (bs : list Byte.byte) : option (catch_clause * list Byte.byte) :=
  match read_u32 bs with
  | Some (tag, tail) =>
      match read_u32 tail with
      | Some (label, rest) => Some (make tag label, rest)
      | None => None
      end
  | None => None
  end.

Definition read_untagged_catch (make : labelidx -> catch_clause)
    (bs : list Byte.byte) : option (catch_clause * list Byte.byte) :=
  match read_u32 bs with
  | Some (label, rest) => Some (make label, rest)
  | None => None
  end.

Definition read_catch (bs : list Byte.byte)
    : option (catch_clause * list Byte.byte) :=
  match bs with
  | x00 :: tail => read_tagged_catch Catch tail
  | x01 :: tail => read_tagged_catch Catch_ref tail
  | x02 :: tail => read_untagged_catch Catch_all tail
  | x03 :: tail => read_untagged_catch Catch_all_ref tail
  | _ => None
  end.

(** Binary grammar, independent of the executable decoder. No legacy EH
    opcodes are accepted as catch-clause discriminants. *)
Inductive catch_binary : list Byte.byte -> catch_clause -> list Byte.byte -> Prop :=
| Binary_catch bs tail rest x l :
    unsigned32 5 bs x tail -> unsigned32 5 tail l rest ->
    catch_binary (x00 :: bs) (Catch x l) rest
| Binary_catch_ref bs tail rest x l :
    unsigned32 5 bs x tail -> unsigned32 5 tail l rest ->
    catch_binary (x01 :: bs) (Catch_ref x l) rest
| Binary_catch_all bs rest l :
    unsigned32 5 bs l rest ->
    catch_binary (x02 :: bs) (Catch_all l) rest
| Binary_catch_all_ref bs rest l :
    unsigned32 5 bs l rest ->
    catch_binary (x03 :: bs) (Catch_all_ref l) rest.

Lemma read_tagged_catch_spec make bs c rest :
  read_tagged_catch make bs = Some (c, rest) <->
  exists x l tail, unsigned32 5 bs x tail /\
    unsigned32 5 tail l rest /\ c = make x l.
Proof.
  unfold read_tagged_catch; split.
  - destruct (read_u32 bs) as [[x tail]|] eqn:Hx; [|discriminate].
    destruct (read_u32 tail) as [[l rest']|] eqn:Hl; [|discriminate].
    intro H; inversion H; subst.
    exists x, l, tail; split; [apply read_u32_correct; assumption|].
    split; [apply read_u32_correct; assumption|reflexivity].
  - intros [x [l [tail [Hx [Hl Heq]]]]]; subst.
    apply read_u32_correct in Hx; apply read_u32_correct in Hl.
    rewrite Hx, Hl; reflexivity.
Qed.

Lemma read_untagged_catch_spec make bs c rest :
  read_untagged_catch make bs = Some (c, rest) <->
  exists l, unsigned32 5 bs l rest /\ c = make l.
Proof.
  unfold read_untagged_catch; split.
  - destruct (read_u32 bs) as [[l rest']|] eqn:Hl; [|discriminate].
    intro H; inversion H; subst; exists l; split; [|reflexivity].
    apply read_u32_correct; assumption.
  - intros [l [Hl Heq]]; subst.
    apply read_u32_correct in Hl; rewrite Hl; reflexivity.
Qed.

Theorem read_catch_correct bs c rest :
  read_catch bs = Some (c, rest) <-> catch_binary bs c rest.
Proof.
  split.
  - destruct bs as [|b bs]; [discriminate|].
    destruct b; simpl; try discriminate.
    + rewrite read_tagged_catch_spec.
      intros [x [l [tail [Hx [Hl Heq]]]]]; subst; econstructor; eauto.
    + rewrite read_tagged_catch_spec.
      intros [x [l [tail [Hx [Hl Heq]]]]]; subst; econstructor; eauto.
    + rewrite read_untagged_catch_spec.
      intros [l [Hl Heq]]; subst; constructor; assumption.
    + rewrite read_untagged_catch_spec.
      intros [l [Hl Heq]]; subst; constructor; assumption.
  - intro H; destruct H; simpl.
    + apply read_tagged_catch_spec; eauto 6.
    + apply read_tagged_catch_spec; eauto 6.
    + apply read_untagged_catch_spec; eauto.
    + apply read_untagged_catch_spec; eauto.
Qed.

Corollary catch_binary_deterministic bs c1 rest1 c2 rest2 :
  catch_binary bs c1 rest1 -> catch_binary bs c2 rest2 ->
  c1 = c2 /\ rest1 = rest2.
Proof.
  intros H1 H2.
  apply read_catch_correct in H1; apply read_catch_correct in H2.
  rewrite H1 in H2; inversion H2; auto.
Qed.

(** Printer uses the repository's existing LEB128 encoder. Its general
    correspondence with this decoder is NOT established by the decoder
    correctness theorem above. Indices in syntax must also be bounded u32s. *)
Definition binary_of_catch (c : catch_clause) : list Byte.byte :=
  match c with
  | Catch x l => x00 :: encode_unsigned x ++ encode_unsigned l
  | Catch_ref x l => x01 :: encode_unsigned x ++ encode_unsigned l
  | Catch_all l => x02 :: encode_unsigned l
  | Catch_all_ref l => x03 :: encode_unsigned l
  end.

End EHBinary.
