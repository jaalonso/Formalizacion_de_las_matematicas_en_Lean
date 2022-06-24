------------------------------------------------------------------------
-- Teoría elemental de funciones
------------------------------------------------------------------------

import tactic

open function

variables {X Y Z : Type}
variables (a b x : X)
variable  (y : Y)
variable  (z : Z)
variables {f : X → Y}
variable  {g : Y → Z}

------------------------------------------------------------------------
-- § Funciones inyectivas                                             --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que
--    injective f ↔ ∀ a b : X, f a = f b → a = b
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  injective f ↔ ∀ a b : X, f a = f b → a = b :=
by refl

-- 2ª demostración
example :
  injective f ↔ ∀ a b : X, f a = f b → a = b :=
-- by library_search
iff.rfl

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    id x = x
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  id x = x :=
rfl

-- 1ª demostración
example :
  id x = x :=
-- by library_search
id.def x

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que la función identidad es inyectiva
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  injective (id : X → X) :=
begin
  unfold injective,
  intros a b hab,
  rw id.def at hab,
  rw id.def at hab,
  exact hab,
end

-- 2ª demostración
example :
  injective (id : X → X) :=
begin
  intros a b hab,
  rw id.def at hab,
  rw id.def at hab,
  exact hab,
end

-- 3ª demostración
example :
  injective (id : X → X) :=
begin
  intros a b hab,
  iterate 2 {rw id.def at hab},
  exact hab,
end

-- 4ª demostración
example :
  injective (id : X → X) :=
begin
  intros a b hab,
  exact hab,
end

-- 5ª demostración
example :
  injective (id : X → X) :=
λ a b hab, hab

-- 6ª demostración
example :
  injective (id : X → X) :=
-- by library_search
injective_id

-- 7ª demostración
example :
  injective (id : X → X) :=
-- by hint
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    (g ∘ f) x = g (f x)
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  (g ∘ f) x = g (f x) :=
rfl

-- 2ª demostración
example :
  (g ∘ f) x = g (f x) :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que la composición de dos funciones inyectivas
-- es inyectiva.
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (hf : injective f)
  (hg : injective g)
  : injective (g ∘ f) :=
begin
  intros a b h,
  apply hf,
  apply hg,
  exact h,
end

-- 2ª demostración
example
  (hf : injective f)
  (hg : injective g)
  : injective (g ∘ f) :=
begin
  intros a b h,
  exact hf (hg h),
end

-- 3ª demostración
example
  (hf : injective f)
  (hg : injective g)
  : injective (g ∘ f) :=
λ a b h, hf (hg h)

-- 3ª demostración
example
  (hf : injective f)
  (hg : injective g)
  : injective (g ∘ f) :=
-- by library_search
injective.comp hg hf

------------------------------------------------------------------------
-- § Funciones suprayectivas                                          --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que
--    surjective f ↔ ∀ y : Y, ∃ x : X, f x = y
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
by refl

-- 2ª demostración
example :
  surjective f ↔ ∀ y : Y, ∃ x : X, f x = y :=
-- by library_search
iff.rfl

-- ---------------------------------------------------------------------
-- Ejercicio 7. Demostrar que la función identidad es suprayectiva.
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  surjective (id : X → X) :=
begin
  intro x,
  use x,
  refl,
end

-- 2ª demostración
example :
  surjective (id : X → X) :=
λ x, ⟨x, rfl⟩

-- 3ª demostración
example :
  surjective (id : X → X) :=
-- by library_search
surjective_id

-- 4ª demostración
example :
  surjective (id : X → X) :=
-- by hint
by tauto

-- ---------------------------------------------------------------------
-- Ejercicio 8. Demostrar que la composición de dos funciones
-- suprayectivas es supreyectiva.
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  intro z,
  cases hg z with y hy,
  cases hf y with x hx,
  use x,
  show g(f(x)) = z,
  rw hx,
  exact hy,
end

-- 2ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
begin
  intro z,
  cases hg z with y hy,
  cases hf y with x hx,
  use x,
  dsimp,
  convert hy,
end

-- 3ª demostración
example
  (hf : surjective f)
  (hg : surjective g)
  : surjective (g ∘ f) :=
-- by library_search
surjective.comp hg hf

------------------------------------------------------------------------
-- § Funciones biyectivas                                             --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 9. Demostrar que
--    bijective f ↔ injective f ∧ surjective f
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  bijective f ↔ injective f ∧ surjective f :=
by refl

-- 2ª demostración
example :
  bijective f ↔ injective f ∧ surjective f :=
-- by suggest
iff.rfl

-- ---------------------------------------------------------------------
-- Ejercicio 10. Demostrar que la función identidad es biyectiva.
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  bijective (id : X → X) :=
⟨injective_id, surjective_id⟩

-- 2ª demostración
example :
  bijective (id : X → X) :=
-- by library_search
bijective_id

-- ---------------------------------------------------------------------
-- Ejercicio 12. Demostrar que la composición de dos funciones biyectivas
-- es biyectiva.
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (hf : bijective f)
  (hg : bijective g)
  : bijective (g ∘ f) :=
begin
  cases hf with hfi hfs,
  cases hg with hgi hgs,
  exact ⟨injective.comp hgi hfi,
         surjective.comp hgs hfs⟩
end

-- =====================================================================
-- § Referencias                                                      --
-- =====================================================================

-- + Kevin Buzzard. "Formalising mathematics : workshop 1 — logic, sets,
--   functions, relations" https://bit.ly/3kJo231
-- + Kevin Buzzard. formalising-mathematics: Part_C_functions.lean
--   https://bit.ly/3EWExRb
-- + Kevin Buzzard. formalising-mathematics: Part_C_functions_solutions.lean
--   https://bit.ly/3CPs1Ba
