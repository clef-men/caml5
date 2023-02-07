From Coq Require Import
  String.

From caml5 Require Import
  prelude.

Class PrettyProjection (X : Type) (str : string) := {
  pretty_projection_type : Type ;
  pretty_projection : X → pretty_projection_type ;
}.
#[global] Arguments Build_PrettyProjection {_ _ _} _.
Notation "x '.«' str »" := (@pretty_projection _ str _ x)
( at level 5,
  only parsing
).
