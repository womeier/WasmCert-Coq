(** Independent final-EH catch grammar on the actual production parser.
    Includes padded indices and arbitrary suffixes; not a whole-module claim. *)
From Stdlib Require Import List Strings.Byte NArith Arith Lia.
From parseque Require Import Parseque.
From Wasm Require Import datatypes binary_format_parser
  binary_format_parser_properties binary_parser_combinator_properties
  binary_parser_lookahead_properties leb128_properties.
Local Notation byte := Byte.byte.

Definition eh_index_encoding bytes x :=
  unsigned_leb bytes x /\ (x <= 4294967295)%N /\ length bytes <= 5.

Lemma eh_index_sound n :
  parser_sound (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n))
    eh_index_encoding.
Proof.
  intros m bound input s Run.
  destruct (parse_u32_prefix_sound n _ _ _ _ Run) as [prefix [Bytes Enc]].
  destruct (parse_u32_as_N_guards bound input s Run) as [Range Width].
  exists prefix; split; [exact Bytes |].
  split; [exact Enc |]. split; [exact Range |].
  pose proof (@Sized.sized _ _ _ input) as Lin.
  pose proof (@Sized.sized _ _ _ (Success.leftovers s)) as Lout.
  change (length (input_bytes input) = m) in Lin.
  change (length (output_bytes s) = Success.size s) in Lout.
  rewrite Bytes, length_app in Lin.
  assert (Count : m - Success.size s = length prefix) by lia.
  rewrite Count in Width.
  lia.
Qed.

Definition eh_one_index {A} (make : N -> A) bytes value :=
  exists x, eh_index_encoding bytes x /\ value = make x.
Definition eh_two_indices {A} (make : N -> N -> A) bytes value :=
  exists xs ys x y, bytes = xs ++ ys /\
    eh_index_encoding xs x /\ eh_index_encoding ys y /\ value = make x y.
Definition eh_prefixed {A} opcode (P : list byte -> A -> Prop) bytes value :=
  exists body, bytes = opcode :: body /\ P body value.

Lemma eh_one_sound {A} n (make : N -> A) :
  parser_sound
    (Combinators.map make (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n)))
    (eh_one_index make).
Proof.
  eapply parser_sound_map; [apply eh_index_sound |].
  intros bytes x Enc; exists x; auto.
Qed.

Lemma eh_one_complete {A} n (make : N -> A) :
  parser_complete
    (Combinators.map make (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n)))
    (eh_one_index make).
Proof.
  eapply parser_complete_map; [apply parse_u32_prefix_complete |].
  intros bytes value [x [Enc Value]]; exists x; auto.
Qed.

Lemma eh_two_sound {A} n (make : N -> N -> A) :
  parser_sound
    (Combinators.app
      (Combinators.map make (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n)))
      (box parse_u32_as_N))
    (eh_two_indices make).
Proof.
  eapply parser_sound_app with (P := eh_one_index make) (Q := eh_index_encoding).
  - apply eh_one_sound.
  - intros k lt; simpl; apply parser_sound_le_lower; apply eh_index_sound.
  - intros xs ys f y [x [X ->]] Y.
    exists xs, ys, x, y; auto.
Qed.

Lemma eh_two_complete {A} n (make : N -> N -> A) :
  parser_complete
    (Combinators.app
      (Combinators.map make (parse_u32_as_N (Toks := SizedList byte) (M := option) (n := n)))
      (box parse_u32_as_N))
    (eh_two_indices make).
Proof.
  eapply parser_complete_app with (P := eh_one_index make) (Q := eh_index_encoding).
  - apply eh_one_complete.
  - intros k lt; simpl; apply parser_complete_le_lower; apply parse_u32_prefix_complete.
  - intros bytes value [xs [ys [x [y [Bytes [X [Y Value]]]]]]].
    exists xs, ys, (make x), y.
    split; [exact Bytes |]. split; [exists x; auto |].
    split; assumption.
Qed.

Lemma eh_prefixed_sound {A n} opcode
    (p : Parser (SizedList byte) byte option A n) P :
  parser_sound p P ->
  parser_sound (Combinators.rand (exact_byte opcode) (box p)) (eh_prefixed opcode P).
Proof.
  intro Sound.
  change (parser_sound (Combinators.bind (exact_byte opcode) (fun _ => box p))
    (eh_prefixed opcode P)).
  eapply parser_sound_bind with
    (P := fun bytes b => bytes = opcode :: nil /\ b = opcode) (Q := fun _ => P).
  - apply parser_sound_exact_byte.
  - intros b k lt; simpl; apply parser_sound_le_lower; exact Sound.
  - intros xs ys b a [-> _] Enc; exists ys; auto.
Qed.

Lemma eh_prefixed_complete {A n} opcode
    (p : Parser (SizedList byte) byte option A n) P :
  parser_complete p P ->
  parser_complete (Combinators.rand (exact_byte opcode) (box p)) (eh_prefixed opcode P).
Proof.
  intro Complete; eapply parser_complete_prefix_byte.
  - intros k lt; simpl; apply parser_complete_le_lower; exact Complete.
  - intros bytes a Enc; exact Enc.
Qed.

Inductive catch_clause_encoding : list byte -> catch_clause -> Prop :=
| encode_catch_tag : forall bytes clause,
    eh_prefixed x00 (eh_two_indices Catch_tag) bytes clause ->
    catch_clause_encoding bytes clause
| encode_catch_all : forall bytes clause,
    eh_prefixed x02 (eh_one_index Catch_all) bytes clause ->
    catch_clause_encoding bytes clause
| encode_catch_tag_ref : forall bytes clause,
    eh_prefixed x01 (eh_two_indices Catch_tag_ref) bytes clause ->
    catch_clause_encoding bytes clause
| encode_catch_all_ref : forall bytes clause,
    eh_prefixed x03 (eh_one_index Catch_all_ref) bytes clause ->
    catch_clause_encoding bytes clause.

Theorem parse_catch_clause_sound n :
  parser_sound (parse_catch_clause (Toks := SizedList byte) (M := option) (n := n))
    catch_clause_encoding.
Proof.
  unfold parse_catch_clause.
  do 3 (apply parser_sound_alt; [shelve |]). Unshelve.
  all: eapply parser_sound_weaken;
    [apply eh_prefixed_sound; first [apply eh_two_sound |apply eh_one_sound] |].
  all: intros bytes clause Enc; now constructor.
Qed.

Ltac eh_catch_initial :=
  apply parser_initial_rand; apply exact_byte_initial.

Ltac eh_catch_select opcode :=
  first
    [solve [apply parser_complete_alt_left; apply eh_prefixed_complete;
       first [apply eh_two_complete |apply eh_one_complete]]
    |eapply parser_complete_alt_right_initial with (actual := opcode);
       [eh_catch_initial |discriminate |
        let bs := fresh "bs" in let c := fresh "c" in
        let body := fresh "body" in let E := fresh "E" in
        intros bs c [body [E _]]; exists body; exact E |
        eh_catch_select opcode]
    |apply eh_prefixed_complete; first [apply eh_two_complete |apply eh_one_complete]].

Theorem parse_catch_clause_complete n :
  parser_complete (parse_catch_clause (Toks := SizedList byte) (M := option) (n := n))
    catch_clause_encoding.
Proof.
  intros m bound input prefix suffix clause Bytes Encoding.
  destruct Encoding as [prefix clause Enc|prefix clause Enc|prefix clause Enc|prefix clause Enc].
  - assert (Complete : parser_complete
        (parse_catch_clause (Toks := SizedList byte) (M := option) (n := n))
        (eh_prefixed x00 (eh_two_indices Catch_tag))).
    { unfold parse_catch_clause.
      apply parser_complete_alt_left.
      apply eh_prefixed_complete.
      apply eh_two_complete. }
    exact (Complete m bound input prefix suffix clause Bytes Enc).
  all: match type of Enc with
  | eh_prefixed ?opcode ?P _ _ =>
      assert (Complete : parser_complete
        (parse_catch_clause (Toks := SizedList byte) (M := option) (n := n))
        (eh_prefixed opcode P))
        by (unfold parse_catch_clause; eh_catch_select opcode);
      exact (Complete m bound input prefix suffix clause Bytes Enc)
  end.
Qed.

Theorem run_parse_catch_clause_correct bytes clause rest :
  run_parse_prefix (fun n => parse_catch_clause (n := n)) bytes = Some (clause, rest) <->
  exists prefix, bytes = prefix ++ rest /\ catch_clause_encoding prefix clause.
Proof.
  split.
  - apply run_parse_prefix_sound; exact parse_catch_clause_sound.
  - intros [prefix [Bytes Enc]]; subst bytes.
    destruct (parse_catch_clause_complete (length (prefix ++ rest)) _
      (Nat.le_refl _) (mkSizedList (prefix ++ rest))
      prefix rest clause Logic.eq_refl Enc) as [s [Run [Value Rest]]].
    unfold run_parse_prefix; rewrite Run.
    change (Some (Success.value s, output_bytes s) = Some (clause, rest)).
    now rewrite Value, Rest.
Qed.

Definition tag_type_encoding := eh_prefixed x00 eh_index_encoding.

Theorem parse_tag_sound n :
  parser_sound (parse_tag (Toks := SizedList byte) (M := option) (n := n))
    tag_type_encoding.
Proof.
  unfold parse_tag, tag_type_encoding, parse_typeidx.
  apply eh_prefixed_sound; apply eh_index_sound.
Qed.

Theorem parse_tag_complete n :
  parser_complete (parse_tag (Toks := SizedList byte) (M := option) (n := n))
    tag_type_encoding.
Proof.
  unfold parse_tag, tag_type_encoding, parse_typeidx.
  apply eh_prefixed_complete; apply parse_u32_prefix_complete.
Qed.

Definition tag_import_encoding := eh_prefixed x04
  (eh_prefixed x00 (eh_one_index MID_tag)).
Definition tag_export_encoding := eh_prefixed x04 (eh_one_index MED_tag).

Ltac eh_skip_descriptor opcode :=
  eapply parser_complete_alt_right_initial with (actual := opcode);
    [eh_catch_initial |discriminate |
     let bs := fresh "bs" in let c := fresh "c" in
     let body := fresh "body" in let E := fresh "E" in
     intros bs c [body [E _]]; exists body; exact E |].

Theorem parse_tag_import_complete n :
  parser_complete (parse_import_desc (Toks := SizedList byte) (M := option) (n := n))
    tag_import_encoding.
Proof.
  unfold parse_import_desc, tag_import_encoding.
  do 4 (eh_skip_descriptor x04).
  apply eh_prefixed_complete; apply eh_prefixed_complete; apply eh_one_complete.
Qed.

Theorem parse_tag_export_complete n :
  parser_complete (parse_module_export_desc (Toks := SizedList byte) (M := option) (n := n))
    tag_export_encoding.
Proof.
  unfold parse_module_export_desc, tag_export_encoding.
  do 4 (eh_skip_descriptor x04).
  apply eh_prefixed_complete; apply eh_one_complete.
Qed.

Definition throw_encoding := eh_prefixed x08 (eh_one_index BI_throw).

Theorem parse_throw_sound n :
  parser_sound (parse_throw (Toks := SizedList byte) (M := option) (n := n))
    throw_encoding.
Proof.
  unfold parse_throw, throw_encoding; apply eh_prefixed_sound; apply eh_one_sound.
Qed.

Theorem parse_throw_complete n :
  parser_complete (parse_throw (Toks := SizedList byte) (M := option) (n := n))
    throw_encoding.
Proof.
  unfold parse_throw, throw_encoding; apply eh_prefixed_complete; apply eh_one_complete.
Qed.

Theorem parse_throw_ref_sound n :
  parser_sound (parse_throw_ref (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => bytes = x0a :: nil /\ value = BI_throw_ref).
Proof.
  unfold parse_throw_ref, Combinators.cmap.
  eapply parser_sound_map; [apply parser_sound_exact_byte |].
  intros bytes b [Bytes _]; auto.
Qed.

Theorem parse_throw_ref_complete n :
  parser_complete (parse_throw_ref (Toks := SizedList byte) (M := option) (n := n))
    (fun bytes value => bytes = x0a :: nil /\ value = BI_throw_ref).
Proof.
  unfold parse_throw_ref, Combinators.cmap.
  eapply parser_complete_map; [apply parser_complete_exact_byte |].
  intros bytes value [Bytes Value]; exists x0a; auto.
Qed.
