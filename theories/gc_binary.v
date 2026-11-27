(** Verified prefix codecs for the GC abstract heap/reference fragment.
    These functions consume exactly their own bytes and preserve the suffix.
    They are not a replacement for the existing whole-module parser.

    Pinned source: WebAssembly/spec d7aada502455b3d9176ca4cbe48be4724d511d2a,
    document/core/binary/types.rst (wasm-3.0).
    Exception types belong to the exception proposal; defined type indices
    require the shared typed-reference representation and are not parsed here. *)
From Wasm Require Import gc_types.
From Stdlib Require Import Strings.Byte List.
Import ListNotations.

Definition encode_abstract_heap (h : abstract_heap_type) : byte :=
  match h with
  | AH_any => x6e | AH_eq => x6d | AH_i31 => x6c
  | AH_struct => x6b | AH_array => x6a | AH_none => x71
  | AH_func => x70 | AH_nofunc => x73
  | AH_extern => x6f | AH_noextern => x72
  end.

Definition decode_abstract_heap (b : byte) : option abstract_heap_type :=
  match b with
  | x6e => Some AH_any | x6d => Some AH_eq | x6c => Some AH_i31
  | x6b => Some AH_struct | x6a => Some AH_array | x71 => Some AH_none
  | x70 => Some AH_func | x73 => Some AH_nofunc
  | x6f => Some AH_extern | x72 => Some AH_noextern
  | _ => None
  end.

Inductive abstract_heap_encoding : byte -> abstract_heap_type -> Prop :=
| ahe_any : abstract_heap_encoding x6e AH_any
| ahe_eq : abstract_heap_encoding x6d AH_eq
| ahe_i31 : abstract_heap_encoding x6c AH_i31
| ahe_struct : abstract_heap_encoding x6b AH_struct
| ahe_array : abstract_heap_encoding x6a AH_array
| ahe_none : abstract_heap_encoding x71 AH_none
| ahe_func : abstract_heap_encoding x70 AH_func
| ahe_nofunc : abstract_heap_encoding x73 AH_nofunc
| ahe_extern : abstract_heap_encoding x6f AH_extern
| ahe_noextern : abstract_heap_encoding x72 AH_noextern.

Lemma decode_abstract_heap_correct b h :
  decode_abstract_heap b = Some h <-> abstract_heap_encoding b h.
Proof.
  split.
  - destruct b; simpl; intro H; try discriminate;
      inversion H; constructor.
  - intro H; destruct H; reflexivity.
Qed.

Lemma abstract_heap_codec_roundtrip h :
  decode_abstract_heap (encode_abstract_heap h) = Some h.
Proof. destruct h; reflexivity. Qed.

Lemma abstract_heap_codec_canonical b h :
  decode_abstract_heap b = Some h -> encode_abstract_heap h = b.
Proof.
  rewrite decode_abstract_heap_correct. intro H; destruct H; reflexivity.
Qed.

Definition read_abstract_heap (bs : list byte) :
    option (abstract_heap_type * list byte) :=
  match bs with
  | [] => None
  | b :: rest =>
      match decode_abstract_heap b with
      | Some h => Some (h, rest)
      | None => None
      end
  end.

(** The printer chooses the abbreviated nullable form.  The decoder also
    accepts the explicit nullable form, as required by the binary grammar. *)
Definition encode_abstract_reference (t : abstract_reference_type) : list byte :=
  if t.(art_nullable)
  then [encode_abstract_heap t.(art_heap)]
  else [x64; encode_abstract_heap t.(art_heap)].

Definition read_explicit_reference (nullable : bool) (bs : list byte) :
    option (abstract_reference_type * list byte) :=
  match read_abstract_heap bs with
  | Some (h, rest) =>
      Some ({| art_nullable := nullable; art_heap := h |}, rest)
  | None => None
  end.

Definition decode_abstract_reference (bs : list byte) :
    option (abstract_reference_type * list byte) :=
  match bs with
  | [] => None
  | x63 :: rest => read_explicit_reference true rest
  | x64 :: rest => read_explicit_reference false rest
  | b :: rest =>
      match decode_abstract_heap b with
      | Some h => Some ({| art_nullable := true; art_heap := h |}, rest)
      | None => None
      end
  end.

Inductive abstract_reference_encoding :
    list byte -> abstract_reference_type -> list byte -> Prop :=
| are_short : forall b h rest,
    abstract_heap_encoding b h ->
    abstract_reference_encoding (b :: rest)
      {| art_nullable := true; art_heap := h |} rest
| are_nullable : forall b h rest,
    abstract_heap_encoding b h ->
    abstract_reference_encoding (x63 :: b :: rest)
      {| art_nullable := true; art_heap := h |} rest
| are_nonnull : forall b h rest,
    abstract_heap_encoding b h ->
    abstract_reference_encoding (x64 :: b :: rest)
      {| art_nullable := false; art_heap := h |} rest.

Lemma read_explicit_reference_correct n bs t rest :
  read_explicit_reference n bs = Some (t, rest) <->
  exists b h, bs = b :: rest /\ abstract_heap_encoding b h /\
    t = {| art_nullable := n; art_heap := h |}.
Proof.
  destruct bs as [|b tail]; simpl.
  - split; [discriminate | intros [b [h [H _]]]; discriminate].
  - unfold read_explicit_reference, read_abstract_heap.
    destruct (decode_abstract_heap b) as [h|] eqn:H; simpl.
    + split.
      * intro E; inversion E; subst.
        exists b, h. repeat split; auto.
        now apply decode_abstract_heap_correct.
      * intros [b' [h' [E [D T]]]].
        inversion E; subst.
        apply decode_abstract_heap_correct in D.
        rewrite H in D; inversion D; subst. reflexivity.
    + split; [discriminate |].
      intros [b' [h' [E [D T]]]].
      inversion E; subst.
      apply decode_abstract_heap_correct in D. congruence.
Qed.

Lemma decode_abstract_reference_sound bs t rest :
  decode_abstract_reference bs = Some (t, rest) ->
  abstract_reference_encoding bs t rest.
Proof.
  destruct bs as [|b tail]; [discriminate |].
  destruct b; simpl; try discriminate;
    try (intro H; inversion H; subst; constructor; constructor).
  all: intro H; apply read_explicit_reference_correct in H;
    destruct H as [b [h [E [D T]]]]; subst; constructor; assumption.
Qed.

Lemma decode_abstract_reference_complete bs t rest :
  abstract_reference_encoding bs t rest ->
  decode_abstract_reference bs = Some (t, rest).
Proof.
  intro H; destruct H; destruct H; reflexivity.
Qed.

Lemma decode_abstract_reference_correct bs t rest :
  decode_abstract_reference bs = Some (t, rest) <->
  abstract_reference_encoding bs t rest.
Proof.
  split; [apply decode_abstract_reference_sound |
          apply decode_abstract_reference_complete].
Qed.

Lemma abstract_reference_codec_roundtrip t rest :
  decode_abstract_reference (encode_abstract_reference t ++ rest) =
  Some (t, rest).
Proof. destruct t as [n h]; destruct n, h; reflexivity. Qed.

Lemma abstract_reference_codec_consumes bs t rest :
  decode_abstract_reference bs = Some (t, rest) ->
  exists prefix, bs = prefix ++ rest /\
    (length prefix = 1 \/ length prefix = 2).
Proof.
  intro H; apply decode_abstract_reference_sound in H; destruct H.
  - exists [b]. split; [reflexivity | now left].
  - exists [x63; b]. split; [reflexivity | now right].
  - exists [x64; b]. split; [reflexivity | now right].
Qed.

Definition encode_packed_type (t : packed_type) : byte :=
  match t with PT_i8 => x78 | PT_i16 => x77 end.

Definition decode_packed_type (b : byte) : option packed_type :=
  match b with x78 => Some PT_i8 | x77 => Some PT_i16 | _ => None end.

Inductive packed_type_encoding : byte -> packed_type -> Prop :=
| pte_i8 : packed_type_encoding x78 PT_i8
| pte_i16 : packed_type_encoding x77 PT_i16.

Lemma decode_packed_type_correct b t :
  decode_packed_type b = Some t <-> packed_type_encoding b t.
Proof.
  split.
  - destruct b; simpl; intro H; try discriminate;
      inversion H; constructor.
  - intro H; destruct H; reflexivity.
Qed.

Lemma packed_type_codec_roundtrip t :
  decode_packed_type (encode_packed_type t) = Some t.
Proof. destruct t; reflexivity. Qed.
