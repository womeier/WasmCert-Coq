(** Compositional residual-stream semantics for the actual option/Parseque
    instance used by binary input. *)
From Stdlib Require Import List Strings.Byte Arith.
From parseque Require Import Parseque.
From Wasm Require Import binary_codec.

Definition byte_parser_family (A: Type) :=
  forall n, Parser (SizedList byte) byte option A n.

Definition prefix_semantics {A} (p: byte_parser_family A)
  (f: list byte -> option (A * list byte)) :=
  forall n input (Hbound: List.length input <= n),
    observe_prefix (runParser (p n) Hbound (mkSizedList input)) = f input.

Lemma prefix_fail : forall A,
  prefix_semantics (fun n => (Combinators.fail:
    Parser (SizedList byte) byte option A n)) (fun _ => None).
Proof. intros A n input Hbound. reflexivity. Qed.

Lemma prefix_anyTok :
  prefix_semantics (fun n =>
    (Combinators.anyTok: Parser (SizedList byte) byte option byte n))
    (fun input => match input with
                  | nil => None
                  | b :: rest => Some (b, rest)
                  end).
Proof.
  intros n [|b rest] Hbound; [reflexivity|].
  cbn. reflexivity.
Qed.

Lemma prefix_map : forall A B (p: byte_parser_family A) f (g: A -> B),
  prefix_semantics p f ->
  prefix_semantics (fun n => Combinators.map g (p n))
    (fun input => option_map (fun '(a, rest) => (g a, rest)) (f input)).
Proof.
  intros A B p f g Hp n input Hbound.
  rewrite <- (Hp n input Hbound).
  unfold Combinators.map. cbn [runParser].
  destruct (runParser (p n) Hbound (mkSizedList input)); reflexivity.
Qed.

Lemma prefix_guardM : forall A B (p: byte_parser_family A) f (g: A -> option B),
  prefix_semantics p f ->
  prefix_semantics (fun n => Combinators.guardM g (p n))
    (fun input =>
      match f input with
      | Some (a, rest) => option_map (fun b => (b, rest)) (g a)
      | None => None
      end).
Proof.
  intros A B p f g Hp n input Hbound.
  rewrite observe_guardM, Hp. reflexivity.
Qed.

Lemma prefix_alt : forall A (p q: byte_parser_family A) f g,
  prefix_semantics p f ->
  prefix_semantics q g ->
  prefix_semantics (fun n => Combinators.alt (p n) (q n))
    (fun input => match f input with Some r => Some r | None => g input end).
Proof.
  intros A p q f g Hp Hq n input Hbound.
  rewrite <- (Hp n input Hbound), <- (Hq n input Hbound).
  unfold Combinators.alt. cbn [runParser].
  destruct (runParser (p n) Hbound (mkSizedList input)); reflexivity.
Qed.

Lemma observe_lift_map : forall A B m n (Hsmall: m < n) (f: A -> B)
  (result: option (Success.Success (SizedList byte) byte A m)),
  observe_prefix (option_map
    (fun s => Success.lt_lift Hsmall (Success.map f s)) result) =
  option_map (fun '(a, rest) => (f a, rest)) (observe_prefix result).
Proof. intros. destruct result; reflexivity. Qed.

Lemma prefix_andbind : forall A B (p: byte_parser_family A)
  (q: A -> byte_parser_family B) f g,
  prefix_semantics p f ->
  (forall a, prefix_semantics (q a) (g a)) ->
  prefix_semantics
    (fun n => Combinators.andbind (p n) (fun a => Combinators.box (q a n)))
    (fun input =>
      match f input with
      | Some (a, rest) => option_map (fun '(b, tail) => ((a, b), tail)) (g a rest)
      | None => None
      end).
Proof.
  intros A B p q f g Hp Hq n input Hbound.
  rewrite <- (Hp n input Hbound).
  unfold Combinators.andbind. cbn [runParser].
  destruct (runParser (p n) Hbound (mkSizedList input))
    as [[a size Hsmall [rest Hsize]]|]; [|reflexivity].
  cbn [observe_prefix].
  subst size.
  unfold Category.bind, Category.fmap.
  cbn -[observe_prefix Success.lt_lift Success.map].
  unfold Success.and.
  cbn -[observe_prefix Success.lt_lift Success.map].
  rewrite observe_lift_map.
  rewrite sized_list_refl.
  rewrite Hq. reflexivity.
Qed.

Lemma prefix_bind : forall A B (p: byte_parser_family A)
  (q: A -> byte_parser_family B) f g,
  prefix_semantics p f ->
  (forall a, prefix_semantics (q a) (g a)) ->
  prefix_semantics
    (fun n => Combinators.bind (p n) (fun a => Combinators.box (q a n)))
    (fun input =>
      match f input with
      | Some (a, rest) => g a rest
      | None => None
      end).
Proof.
  intros A B p q f g Hp Hq n input Hbound.
  unfold Combinators.bind.
  pose proof (prefix_map _ _ _ _ (@snd A B)
    (prefix_andbind A B p q f g Hp Hq) n input Hbound) as Hsem.
  rewrite Hsem.
  destruct (f input) as [[a rest]|]; [|reflexivity].
  destruct (g a rest) as [[b tail]|]; reflexivity.
Qed.

Lemma prefix_and : forall A B (p: byte_parser_family A)
  (q: byte_parser_family B) f g,
  prefix_semantics p f ->
  prefix_semantics q g ->
  prefix_semantics
    (fun n => Combinators.and (p n) (Combinators.box (q n)))
    (fun input =>
      match f input with
      | Some (a, rest) => option_map (fun '(b, tail) => ((a, b), tail)) (g rest)
      | None => None
      end).
Proof.
  intros A B p q f g Hp Hq.
  apply prefix_andbind; [assumption|intros; assumption].
Qed.

Lemma prefix_app : forall A B (p: byte_parser_family (A -> B))
  (q: byte_parser_family A) f g,
  prefix_semantics p f ->
  prefix_semantics q g ->
  prefix_semantics
    (fun n => Combinators.app (p n) (Combinators.box (q n)))
    (fun input =>
      match f input with
      | Some (h, rest) => option_map (fun '(a, tail) => (h a, tail)) (g rest)
      | None => None
      end).
Proof.
  intros A B p q f g Hp Hq.
  change (prefix_semantics
    (fun n => Combinators.bind (p n)
      (fun h => Combinators.box (Combinators.map h (q n))))
    (fun input =>
      match f input with
      | Some (h, rest) => option_map (fun '(a, tail) => (h a, tail)) (g rest)
      | None => None
      end)).
  apply prefix_bind; [assumption|].
  intros h. now apply prefix_map.
Qed.

Lemma prefix_rand : forall A B (p: byte_parser_family A)
  (q: byte_parser_family B) f g,
  prefix_semantics p f ->
  prefix_semantics q g ->
  prefix_semantics
    (fun n => Combinators.rand (p n) (Combinators.box (q n)))
    (fun input => match f input with
                  | Some (_, rest) => g rest
                  | None => None
                  end).
Proof.
  intros A B p q f g Hp Hq n input Hbound.
  unfold Combinators.rand.
  pose proof (prefix_map _ _ _ _ (@snd A B)
    (prefix_and A B p q f g Hp Hq) n input Hbound) as Hsem.
  rewrite Hsem.
  destruct (f input) as [[a rest]|]; [|reflexivity].
  destruct (g rest) as [[b tail]|]; reflexivity.
Qed.
