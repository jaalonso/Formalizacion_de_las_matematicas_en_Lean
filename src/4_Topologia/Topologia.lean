-- =====================================================================
-- § Resumen                                                          --
-- =====================================================================

-- En esta relación se demostrará que
-- + la imagen de un espacio compacto mediante una función continua es
--   compacta.
-- + Los subconjuntos cerrados de un espacio compacto son compactos.
--
-- Concretamente, lo que demostraremos es que
-- + Si `f : X → Y` es una función continua y `S : set X` es un conjunto
--   compacto (con la subtopología), entonces `f '' S` (la imagen de `S`
--   por `f`) es compacto (con la subtopología).
-- + Si `X` es unespacio topológico, `S` es un subconjunto compacto y
--   `C` es un subconjunto cerrado, entonces `S ∩ C` es un subconjunto
--   compacto.
--
-- Los resultados originales son los casos particulares cuando `S` es
-- `univ : set X`.

-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de las propiedades de los subconjuntos
-- de los espacios topológicos.
-- ---------------------------------------------------------------------

import topology.subset_properties

-- =====================================================================
-- § Introducción                                                     --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar
-- + X e Y como variables sobre espacios topológicos.
-- + f como variable sobre las funciones de x en Y.
-- ---------------------------------------------------------------------

variables (X Y : Type) [topological_space X] [topological_space Y]
variable  (f : X → Y)

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir es espacion de nombre set (de los conjuntos).
-- ---------------------------------------------------------------------

open set

-- =====================================================================
-- § Subespacios compactos                                            --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que un subconjunto de un espacio topológico es
-- compacto si de todo recubrimiento abierto se puede extraer un
-- subrecubrimiento finito.
-- ---------------------------------------------------------------------

lemma compact_iff_finite_subcover'
  {α : Type} [topological_space α]
  {S : set α}
  : is_compact S ↔
    (∀ {ι : Type} (U : ι → set α),
       (∀ i, is_open (U i))
       → S ⊆ (⋃ i, U i)
       → (∃ (t : set ι), t.finite ∧ S ⊆ (⋃ i ∈ t, U i))) :=
begin
  rw compact_iff_finite_subcover,
  split,
  { intros hs ι U hU hsU,
    cases hs U hU hsU with F hF,
    use [(↑F : set ι), finset.finite_to_set F],
    exact hF },
  { intros hs ι U hU hsU,
    rcases hs U hU hsU with ⟨F, hFfin, hF⟩,
    use hFfin.to_finset,
    convert hF,
    ext,
    simp }
end

-- =====================================================================
-- § La imagen continua de compactos es compacta                      --
-- =====================================================================

-- Nota: Lemas útiles sobre topología
-- + is_open_compl_iff
--      {α : Type u} [topological_space α]
--      {s : set α}
--      : is_open sᶜ ↔ is_closed s
-- + is_open_preimage
--      {α : Type u_1} [topological_space α]
--      {β : Type u_2} [topological_space β]
--      {f : α → β}
--      (hf : continuous f)
--      {s : set β}
--      (h : is_open s)
--      : is_open (f ⁻¹' s)




/-!

## Continuous image of compact is compact

I would start with `rw compact_iff_finite_subcover' at hS ⊢,`

The proof that I recommend formalising is this. Say `S` is a compact
subset of `X`, and `f : X → Y` is continuous. We want to prove that
every cover of `f '' S` by open subsets of `Y` has a finite subcover.
So let's cover `f '' S` with opens `U i : set Y`, for `i : ι` and `ι` an index type.
Pull these opens back to `V i : set X` and observe that they cover `S`.
Choose a finite subcover corresponding to some `F : set ι` such that `F` is finite
(Lean writes this `h : F.finite`) and then check that the corresponding cover
of `f '' S` by the `U i` with `i ∈ F` is a finite subcover.

Good luck! Please ask questions (or DM me on discord if you don't want to
ask publically). Also feel free to DM me if you manage to do it!

Useful theorems:

`continuous.is_open_preimage` -- preimage of an open set under a
continuous map is open.

`is_open_compl_iff` -- complement `Sᶜ` of `S` is open iff `S` is closed.

## Some useful tactics:

### `specialize`

`specialize` can be used with `_`. If you have a hypothesis

`hS : ∀ {ι : Type} (U : ι → set X), (∀ (i : ι), is_open (U i)) → ...`

and `U : ι → set X`, then

`specialize hS U` will change `hS` to

`hS : (∀ (i : ι), is_open (U i)) → ...`

But what if you now want to prove `∀ i, is_open (U i)` so you can feed it
into `hS` as an input? You can put

`specialize hS _`

and then that goal will pop out. Unfortunately it pops out _under_ the
current goal! You can swap two goals with the `swap` tactic though :-)

### `change`

If your goal is `⊢ P` and `P` is definitionally equal to `Q`, then you
can write `change Q` and the goal will change to `Q`. Sometimes useful
because rewriting works up to syntactic equality, which is stronger
than definitional equality.

### `rwa`

`rwa h` just means `rw h, assumption`

### `contradiction`

If you have `h1 : P` and `h2 : ¬ P` as hypotheses, then you can prove any goal with
the `contradiction` tactic, which just does `exfalso, apply h2, exact h1`.

### `set`

Note : The `set` tactic is totally unrelated to the `set X` type of subsets of `X`!

The `set` tactic can be used to define things. For example
`set T := f '' S with hT_def,` will define `T` to be `f '' S`
and will also define `hT_def : T = f '' S`.

-/

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es continua y S es compacto, entoces la
-- imagen de S por f es compacto.
-- ---------------------------------------------------------------------


-- La idea de la demostración es la siguiente: Sea `S` un subconjunto
-- compacto de `X` y `f : X → Y` continua. Dado `U i : set Y` un
-- recubrimiento abierto de `f '' S`, para cada `i` se define
-- `V i = f ⁻¹' (U i)`. Se rprueba que `V` es un recubriemiento abierto
-- de `S` y, como `S`es compacto, tiene un subrecubrimiento finito. La
-- imágenes de cada conjunto de dicho subrecubrimiento forman un
-- subrecubrimiento finito de `f '' S`.

lemma image_compact_of_compact
  (hf : continuous f)
  (S : set X)
  (hS : is_compact S)
  : is_compact (f '' S) :=
begin
  rw compact_iff_finite_subcover' at *,
  set T := f '' S with hT_def,
  intros ι U hU hcoverU,
  set V : ι → set X := λ i, f ⁻¹' (U i) with hV_def,
  specialize hS V _,
  swap,
  { intro i,
    rw hV_def, dsimp only,
    apply continuous.is_open_preimage hf _ (hU i), },
  { specialize hS _,
    swap,
    { intros x hx,
      have hfx : f x ∈ T,
      { rw hT_def,
        rw mem_image,
        use x,
        use hx,},
      { specialize hcoverU hfx,
        rw mem_Union at hcoverU ⊢,
        exact hcoverU, }},
    { rcases hS with ⟨F, hFfinite, hF⟩,
      use F,
      use hFfinite,
      rintros y ⟨x, hxs, rfl⟩,
      rw subset_def at hF,
      specialize hF x hxs,
      rw mem_bUnion_iff at hF ⊢,
      exact hF, }},
end

-- =====================================================================
-- § Subconjuntos cerrados de compactos                               --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si S es compacto y C es cerrado, entonces
-- `S ∩ C` es compacto.
-- ---------------------------------------------------------------------


lemma closed_of_compact
  (S : set X)
  (hS : is_compact S)
  (C : set X)
  (hC : is_closed C)
  : is_compact (S ∩ C) :=
begin
  rw compact_iff_finite_subcover' at *,
  intros ι U hUopen hSCcover,
  let V : option ι → set X := λ x, option.rec Cᶜ U x,
  specialize hS V _,
  swap,
  { intros i,
    cases i with i,
    { change is_open Cᶜ,
      rwa is_open_compl_iff },
    { change is_open (U i),
      apply hUopen } },
  specialize hS _,
  swap,
  { intros x hxS,
    by_cases hxC : x ∈ C,
    { rw subset_def at hSCcover,
      specialize hSCcover x ⟨hxS, hxC⟩,
      rw mem_Union at ⊢ hSCcover,
      cases hSCcover with i hi,
      use (some i),
      exact hi },
    { rw mem_Union,
      use none } },
  rcases hS with ⟨F, hFfinite, hFcover⟩,
  use (some : ι → option ι) ⁻¹' F,
  split,
  { apply finite.preimage _ hFfinite,
    intros i hi j hj,
    exact option.some_inj.mp },
  rintros x ⟨hxS, hxC⟩,
  rw subset_def at hFcover,
  specialize hFcover x hxS,
  rw mem_bUnion_iff at hFcover ⊢,
  rcases hFcover with ⟨i, hiF, hxi⟩,
  cases i with i,
  { contradiction },
  { use [i, hiF, hxi] },
end
