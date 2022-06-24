------------------------------------------------------------------------
-- Teoría elemental de conjuntos
------------------------------------------------------------------------

import tactic

variables (Ω : Type)
variables (X Y Z W : set Ω)
variables (a b c x y z : Ω)

------------------------------------------------------------------------
-- § Subconjuntos                                                     --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 1. Demostrar que
--    X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
begin
  refl,
end

-- 2ª demostración
example :
  X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
by refl

-- 3ª demostración
example :
  X ⊆ Y ↔ ∀ a, a ∈ X → a ∈ Y :=
-- by suggest
iff.rfl

-- ---------------------------------------------------------------------
-- Ejercicio 2. Demostrar que
--    X ⊆ X
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ⊆ X :=
begin
  rw set.subset_def,
  intros a ha,
  exact ha,
end

-- 2ª demostración
example :
  X ⊆ X :=
begin
  intros a ha,
  exact ha,
end

-- 3ª demostración
example :
  X ⊆ X :=
by exact λ a ha, ha

-- ---------------------------------------------------------------------
-- Ejercicio 3. Demostrar que
--      X ⊆ Y, Y ⊆ Z ⊢ X ⊆ Z
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (hXY : X ⊆ Y)
  (hYZ : Y ⊆ Z)
  : X ⊆ Z :=
begin
  rw set.subset_def at *,
  intros a ha,
  apply hYZ,
  apply hXY,
  exact ha,
end

-- 2ª demostración
example
  (hXY : X ⊆ Y)
  (hYZ : Y ⊆ Z)
  : X ⊆ Z :=
begin
  intros a ha,
  apply hYZ,
  apply hXY,
  exact ha,
end

-- 3ª demostración
example
  (hXY : X ⊆ Y)
  (hYZ : Y ⊆ Z)
  : X ⊆ Z :=
begin
  intros a ha,
  apply hYZ (hXY ha),
end

-- 4ª demostración
example
  (hXY : X ⊆ Y)
  (hYZ : Y ⊆ Z)
  : X ⊆ Z :=
λ a ha, hYZ (hXY ha)

------------------------------------------------------------------------
-- § Igualdad de conjuntos                                            --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que
--    X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y)
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
begin
  exact set.ext_iff
end

-- 2ª demostración
example :
  X = Y ↔ (∀ a, a ∈ X ↔ a ∈ Y) :=
set.ext_iff

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--      X ⊆ Y, Y ⊆ X ⊢ X = Y
-- ----------------------------------------------------------------------

example
  (hXY : X ⊆ Y)
  (hYX : Y ⊆ X)
  : X = Y :=
begin
  ext a,
  split,
  { apply hXY },
  { apply hYX },
end

------------------------------------------------------------------------
-- § Uniones e intersecciones                                         --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que
--    a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y
-- ----------------------------------------------------------------------

example :
  a ∈ X ∪ Y ↔ a ∈ X ∨ a ∈ Y :=
by refl

-- ---------------------------------------------------------------------
-- Ejercicio 7. Demostrar que
--    a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y
-- ----------------------------------------------------------------------

example :
  a ∈ X ∩ Y ↔ a ∈ X ∧ a ∈ Y :=
by refl

-- ---------------------------------------------------------------------
-- Ejercicio 8. Demostrar que
--    X ∪ X = X
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ∪ X = X :=
begin
  ext a,
  rw set.mem_union,
  split,
  { intro h,
    cases h with ha ha;
    exact ha },
  { intro ha,
    left,
    exact ha }
end

-- 2ª demostración
example :
  X ∪ X = X :=
begin
  ext a,
  split,
  { intro h,
    dsimp at h,
    tauto, },
  { intro ha,
    dsimp,
    tauto, }
end

-- 3ª demostración
example :
  X ∪ X = X :=
begin
  ext a,
  dsimp;
  tauto,
end

-- 4ª demostración
example :
  X ∪ X = X :=
set.union_self X

-- 5ª demostración
example :
  X ∪ X = X :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 9. Demostrar que
--    X ⊆ X ∪ Y
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ⊆ X ∪ Y :=
begin
  rw set.subset_def,
  intros a haX,
  rw set.mem_union,
  left,
  assumption,
end

-- 2ª demostración
example :
  X ⊆ X ∪ Y :=
begin
  intros a haX,
  apply or.inl,
  exact haX,
end

-- 3ª demostración
example :
  X ⊆ X ∪ Y :=
begin
  intros a haX,
  exact or.inl haX,
end

-- 4ª demostración
example :
  X ⊆ X ∪ Y :=
set.subset_union_left X Y

-- 5ª demostración
example :
  X ⊆ X ∪ Y :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 10. Demostrar que
--    Y ⊆ X ∪ Y
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  Y ⊆ X ∪ Y :=
begin
  intros a haY,
  right,
  assumption,
end

-- 2ª demostración
example :
  Y ⊆ X ∪ Y :=
begin
  intros a haY,
  exact or.inr haY,
end

-- 3ª demostración
example :
  Y ⊆ X ∪ Y :=
-- by library_search
set.subset_union_right X Y

-- 4ª demostración
example :
  Y ⊆ X ∪ Y :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 11. Demostrar que
--    X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  { intro h,
    split,
    { intros a haX,
      apply h,
      left,
      assumption },
    { intros a haY,
      apply h,
      right,
      assumption }},
  { rintros ⟨hXZ, hYZ⟩ a (haX | haY),
    { exact hXZ haX },
    { exact hYZ haY } }
end

-- 2ª demostración
example :
  X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  { intro h,
    split,
    { intros a haX,
      exact h (or.inl haX), },
    { intros a haY,
      exact h (or.inr haY)}},
  { rintros ⟨hXZ, hYZ⟩ a (haX | haY),
    { exact hXZ haX },
    { exact hYZ haY } }
end

-- 3ª demostración
example :
  X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
begin
  split,
  { intro h,
    split,
    { exact λ a haX, h (or.inl haX), },
    { exact λ a haY, h (or.inr haY)}},
  { rintros ⟨hXZ, hYZ⟩ a (haX | haY),
    { exact hXZ haX },
    { exact hYZ haY } }
end

-- 3ª demostración
example :
  X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
by finish [iff_def, set.subset_def]

-- 4ª demostración
example :
  X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
-- by library_search
set.union_subset_iff

-- 5ª demostración
example :
  X ∪ Y ⊆ Z ↔ X ⊆ Z ∧ Y ⊆ Z :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 12. Demostrar que
--    W ⊆ X, Y ⊆ Z ⊢ W ∪ Y ⊆ X ∪ Z
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (hWX : W ⊆ X)
  (hYZ : Y ⊆ Z)
  : W ∪ Y ⊆ X ∪ Z :=
begin
  rintros a (haW | haY),
  { left,
    exact hWX haW },
  { right,
    exact hYZ haY }
end

-- 2ª demostración
example
  (hWX : W ⊆ X)
  (hYZ : Y ⊆ Z)
  : W ∪ Y ⊆ X ∪ Z :=
begin
  rintros a (haW | haY),
  { exact or.inl (hWX haW), },
  { exact or.inr (hYZ haY), }
end

-- 3ª demostración
example
  (hWX : W ⊆ X)
  (hYZ : Y ⊆ Z)
  : W ∪ Y ⊆ X ∪ Z :=
by finish [set.subset_def]

-- 4ª demostración
example
  (hWX : W ⊆ X)
  (hYZ : Y ⊆ Z)
  : W ∪ Y ⊆ X ∪ Z :=
-- by library_search
set.union_subset_union hWX hYZ

-- ---------------------------------------------------------------------
-- Ejercicio 13. Demostrar que
--    X ⊆ Y ⊢ X ∪ Z ⊆ Y ∪ Z
-- ----------------------------------------------------------------------

-- 1ª demostración
example
  (hXY : X ⊆ Y)
  : X ∪ Z ⊆ Y ∪ Z :=
begin
  rintros a (haX | haZ),
  { left,
    exact hXY haX },
  { right,
    exact haZ, }
end

-- 2ª demostración
example
  (hXY : X ⊆ Y)
  : X ∪ Z ⊆ Y ∪ Z :=
begin
  rintros a (haX | haZ),
  { exact or.inl (hXY haX), },
  { exact or.inr haZ, }
end

-- 3ª demostración
example
  (hXY : X ⊆ Y)
  : X ∪ Z ⊆ Y ∪ Z :=
by finish [set.subset_def]

-- 4ª demostración
example
  (hXY : X ⊆ Y)
  : X ∪ Z ⊆ Y ∪ Z :=
-- by library_search
set.union_subset_union_left Z hXY

-- ---------------------------------------------------------------------
-- Ejercicio 14. Demostrar que
--    X ∩ Y ⊆ X
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ∩ Y ⊆ X :=
begin
  rintro a ⟨haX, haY⟩,
  assumption,
end

-- 2ª demostración
example :
  X ∩ Y ⊆ X :=
begin
  rintro a ⟨haX, -⟩,
  exact haX,
end

-- 3ª demostración
example :
  X ∩ Y ⊆ X :=
-- by library_search
set.inter_subset_left X Y

-- 4ª demostración
example :
  X ∩ Y ⊆ X :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 15. Demostrar que
--    X ∩ X = X
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ∩ X = X :=
begin
  ext a,
  split,
  { rintro ⟨haX, -⟩,
    exact haX, },
  { intro haX,
    exact ⟨haX, haX⟩ }
end

-- 2ª demostración
example :
  X ∩ X = X :=
set.ext (assume x, and_self _)

-- 3ª demostración
example :
  X ∩ X = X :=
-- by library_search
set.inter_self X

-- 4ª demostración
example :
  X ∩ X = X :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio 16. Demostrar que
--    X ∩ Y = Y ∩ X
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ∩ Y = Y ∩ X :=
begin
  ext a,
  split,
  { rintro ⟨haX, haY⟩,
    exact ⟨haY, haX⟩ },
  { rintro ⟨haY, haX⟩,
    exact ⟨haX, haY⟩ }
end

-- 2ª demostración
example :
  X ∩ Y = Y ∩ X :=
begin
  ext a,
  split;
  { rintro ⟨h1, h2⟩,
    exact ⟨h2, h1⟩ }
end

-- 2ª demostración
example :
  X ∩ Y = Y ∩ X :=
begin
  ext a,
  exact and.comm,
end

-- 3ª demostración
example :
  X ∩ Y = Y ∩ X :=
set.ext (λ x, and.comm)

-- 4ª demostración
example :
  X ∩ Y = Y ∩ X :=
-- by library_search
set.inter_comm X Y

-- 5ª demostración
example :
  X ∩ Y = Y ∩ X :=
-- by hint
by finish

-- ---------------------------------------------------------------------
-- Ejercicio 17. Demostrar que
--    X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  ext a,
  split,
  { rintro ⟨hx, hy, hz⟩,
    exact ⟨⟨hx, hy⟩, hz⟩ },
  { rintro ⟨⟨hx, hy⟩, hz⟩,
    exact ⟨hx, hy, hz⟩ },
end

-- 2ª demostración
example :
  X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
begin
  ext a,
  dsimp,
  exact and.assoc.symm,
end

-- 3ª demostración
example :
  X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
set.ext (λ x, and.assoc.symm)

-- 4ª demostración
example :
  X ∩ (Y ∩ Z) = (X ∩ Y) ∩ Z :=
-- by library_search
(set.inter_assoc X Y Z).symm

------------------------------------------------------------------------
-- § Cuantificadores                                                  --
------------------------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 18. Demostrar que
--    ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X)
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  split,
  { intros h b hb,
    apply h,
    use b,
    exact hb, },
  { rintro h ⟨a, ha⟩,
    exact (h a) ha, },
end

-- 2ª demostración
example :
  ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
begin
  push_neg,
  simp,
end

-- 3ª demostración
example :
  ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
by {push_neg, simp}

-- 3ª demostración
example :
  ¬ (∃ a, a ∈ X) ↔ ∀ b, ¬ (b ∈ X) :=
-- by library_search
not_exists

-- ---------------------------------------------------------------------
-- Ejercicio 19. Demostrar que
--    ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X)
-- ----------------------------------------------------------------------

-- 1ª demostración
example :
  ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
begin
  split,
  { intro h,
    by_contra hnX,
    apply h,
    intro a,
    by_contra hXa,
    apply hnX,
    use a, },
  { intro h,
    cases h with b hb,
    intro h,
    apply hb,
    apply h }
end

-- 2ª demostración
example :
  ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
-- by library_search
not_forall

-- 3ª demostración
example :
  ¬ (∀ a, a ∈ X) ↔ ∃ b, ¬ (b ∈ X) :=
by simp

-- =====================================================================
-- § Referencias                                                      --
-- =====================================================================

-- + Kevin Buzzard. "Formalising mathematics : workshop 1 — logic, sets,
--   functions, relations" https://bit.ly/3kJo231
-- + Kevin Buzzard. formalising-mathematics: Part_B_sets.lean
--   https://bit.ly/2Wiv1Xe
-- + Kevin Buzzard. formalising-mathematics: Part_B_sets_solutions.lean
--   https://bit.ly/3zQyv0Y
