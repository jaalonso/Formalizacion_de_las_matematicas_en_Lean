------------------------------------------------------------------------
-- § Introducción                                                     --
------------------------------------------------------------------------

-- Se importan las tácticas.
import tactic

-- Nota: Las conectivas lógicas son
-- → "condicional"   se escribe con \->
-- ¬ "negación"      se escribe con \not
-- ∧ "conjunción"    se escribe con \and
-- ↔ "bicondicional" se escribe con \<->
-- ∨ "disyunción"    se escribe con \or

-- Nota: Colocando el curso sobre un símbolo y pulsando C-c C-k se
-- indican las formas de escribirlo

-- Nota: Se usarán las siguientes tácticas (que están en
-- https://bit.ly/3pHFhBO )
-- + intro
-- + exact
-- + apply
-- + rw
-- + cases
-- + split
-- + left
-- + right

-- Nota: En https://bit.ly/3pHFhBO se encuentran estas junto con más
-- tácticas. Por ejemplo, cc, tauto, tauto!, finish y library_search.

-- Nota: Para evitar conflictos, se trabajará en el espacio de nombres
-- oculto.
namespace oculto

-- Nota: P, Q y R son variables sobre proposiciones.
variables (P Q R : Prop)

------------------------------------------------------------------------
-- § Implicaciones (→)                                                --
------------------------------------------------------------------------

-- Nota: En esta sección se usarán las tácticas intro, apply, exact y
-- assumption.

-- ----------------------------------------------------
-- Ejercicio 1. Demostrar que
--    P → P
-- ----------------------------------------------------

theorem id :
  P → P :=
begin
  intro hP,
  exact hP
end

-- ----------------------------------------------------
-- Ejercicio 2. Demostrar que el condicional no es
-- asociativa probando que
--    (false → (false → false)) ↔ true
--    ((false → false) → false) ↔ false
-- ----------------------------------------------------

example :
  (false → (false → false)) ↔ true :=
by simp

example :
  ((false → false) → false) ↔ false :=
by simp

-- Nota: En Lean el condicional asocia por la derecha;
-- es decir, (P → Q → R) es P → (Q → R).

-- ----------------------------------------------------
-- Ejercicio 3. Demostrar que
--    (P → Q → R) ↔ (P → (Q → R))
-- ----------------------------------------------------

example : (P → Q → R) ↔ (P → (Q → R)) :=
begin
  refl,
end

-- ----------------------------------------------------
-- Ejercicio 4. Demostrar que
--    P → Q → P
-- ----------------------------------------------------

theorem imp_intro :
  P → Q → P :=
begin
  intro hP,
  intro hQ,
  exact hP,
end

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que
--    P → (P → Q) → Q
-- ----------------------------------------------------------------------

lemma modus_ponens :
  P → (P → Q) → Q :=
begin
  intro hP,
  intro hPQ,
  apply hPQ,
  exact hP,
end

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que
--    (P → Q) → (Q → R) → (P → R)
-- ----------------------------------------------------------------------

lemma imp_trans :
  (P → Q) → (Q → R) → (P → R) :=
begin
  intros hPQ hQR hP,
  apply hQR,
  apply hPQ,
  exact hP,
end

-- ---------------------------------------------------------------------
-- Ejercicio 7. Demostrar que
--    (P → Q → R) → (P → Q) → (P → R)
-- ----------------------------------------------------------------------

lemma forall_imp :
  (P → Q → R) → (P → Q) → (P → R) :=
begin
  intro hPQR,
  intro hPQ,
  intro hP,
  apply hPQR,
  { exact hP, },
  { apply hPQ,
    exact hP, },
end

-------------------------------------------------------
-- § Negación (¬)                                    --
-------------------------------------------------------

-- Nota: La negación ¬P es, por definición (P → false).

-- ---------------------------------------------------------------------
-- Ejercicio 8. Demostrar que
--    ¬ P ↔ (P → false)
-- ----------------------------------------------------------------------

theorem not_def
  : ¬ P ↔ (P → false) :=
begin
  refl,
end

-- ---------------------------------------------------------------------
-- Ejercicio 9. Demostrar que
--    P → ¬¬P
-- ----------------------------------------------------------------------

theorem not_not_intro :
  P → ¬¬P :=
begin
  intro hP,
  rw not_def,
  rw not_def,
  intro hnP,
  apply hnP,
  exact hP,
end

-- 2ª demostración
example :
  P → ¬¬P :=
begin
  intro hP,
  intro hnP,
  apply hnP,
  exact hP,
end

-- 3ª demostración
example :
  P → ¬¬P :=
begin
  intros hP hnP,
  exact hnP hP,
end

-- 4ª demostración
example :
  P → ¬¬P :=
λ hP hnP, hnP hP

-- 5ª demostración
example :
  P → ¬¬P :=
begin
  apply modus_ponens,
end

-- 6ª demostración
example :
  P → ¬¬P :=
-- by library_search
not_not.mpr

-- ---------------------------------------------------------------------
-- Ejercicio 10. Demostrar que
--    (P → Q) → (¬ Q → ¬ P)
-- ----------------------------------------------------------------------

theorem modus_tollens :
  (P → Q) → (¬ Q → ¬ P) :=
begin
  apply imp_trans,
end

-- ---------------------------------------------------------------------
-- Ejercicio 11. Demostrar que
--    ¬¬P → P
-- ----------------------------------------------------------------------

theorem double_negation_elimination :
  ¬¬P → P :=
begin
  intro hnnP,
  by_contra h,
  apply hnnP,
  exact h,
end

-------------------------------------------------------
-- § Conjunción                                      --
-------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 12. Demostrar que
--    P, Q ⊢ P ∧ Q
-- ----------------------------------------------------------------------

example
  (hP : P)
  (hQ : Q)
  : P ∧ Q :=
begin
  split,
  { exact hP, },
  { exact hQ, }
end

-- ---------------------------------------------------------------------
-- Ejercicio 13. Demostrar que
--    P ∧ Q → P
-- ----------------------------------------------------------------------

theorem and.elim_left :
  P ∧ Q → P :=
begin
  intro hPaQ,
  cases hPaQ with hP hQ,
  exact hP,
end

-- ---------------------------------------------------------------------
-- Ejercicio 14. Demostrar que
--    P ∧ Q → Q
-- ----------------------------------------------------------------------

-- 1ª demostración
theorem and.elim_right :
  P ∧ Q → Q :=
begin
  intro hPaQ,
  exact hPaQ.2,
end

-- 2ª demostración
example : P ∧ Q → Q :=
λ hPaQ, hPaQ.2

-- ---------------------------------------------------------------------
-- Ejercicio 15. Demostrar que
--    P → Q → P ∧ Q
-- ----------------------------------------------------------------------


theorem and.intro : P → Q → P ∧ Q :=
begin
  intros hP hQ,
  split,
  { assumption },
  { assumption }
end

-- ---------------------------------------------------------------------
-- Ejercicio 16. Demostrar que
--    P ∧ Q → (P → Q → R) → R
-- ----------------------------------------------------------------------

theorem and.elim :
  P ∧ Q → (P → Q → R) → R :=
begin
  rintro ⟨hP, hQ⟩ hPQR,
  exact hPQR hP hQ,
end

-- ---------------------------------------------------------------------
-- Ejercicio 17. Demostrar que
--    (P → Q → R) → P ∧ Q → R
-- ----------------------------------------------------------------------

theorem and.rec :
  (P → Q → R) → P ∧ Q → R :=
begin
  rintro hPQR ⟨hP, hQ⟩,
  exact hPQR hP hQ,
end

-- ---------------------------------------------------------------------
-- Ejercicio 18. Demostrar que
--    P ∧ Q → Q ∧ P
-- ----------------------------------------------------------------------

-- 1ª demostración
theorem and.symm :
  P ∧ Q → Q ∧ P :=
begin
  rintro ⟨hP, hQ⟩,
  exact ⟨hQ, hP⟩
end

-- 2ª demostración
example : P ∧ Q → Q ∧ P :=
λ ⟨hP, hQ⟩, ⟨hQ, hP⟩

-- ---------------------------------------------------------------------
-- Ejercicio 19. Demostrar que
--    (P ∧ Q) → (Q ∧ R) → (P ∧ R)
-- ----------------------------------------------------------------------

theorem and.trans :
  (P ∧ Q) → (Q ∧ R) → (P ∧ R) :=
begin
  rintro ⟨hP, hQ⟩ ⟨hQ', hR⟩,
  exact ⟨hP, hR⟩,
end

lemma imp_imp_of_and_imp :
  ((P ∧ Q) → R) → (P → Q → R) :=
begin
  intros h hP hQ,
  exact h ⟨hP, hQ⟩
end

-------------------------------------------------------
-- § Bicondicional (↔)                               --
-------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 20. Demostrar que
--    P ↔ P
-- ----------------------------------------------------------------------

-- 1ª demostración
theorem iff.refl :
  P ↔ P :=
begin
  split,
  { apply id },
  { apply id },
end

-- 2ª demostración
example :
  P ↔ P :=
begin
  tauto!,
end

-- 3ª demostración
example :
  P ↔ P :=
begin
  refl
end

-- ---------------------------------------------------------------------
-- Ejercicio 21. Demostrar que
--    (P ↔ Q) → (Q ↔ P)
-- ----------------------------------------------------------------------

-- 1ª demostración
theorem iff.symm :
  (P ↔ Q) → (Q ↔ P) :=
begin
  intro h,
  rw h,
end

-- 2ª demostración
example :
  (P ↔ Q) → (Q ↔ P) :=
λ ⟨hPQ, hQP⟩, ⟨hQP, hPQ⟩

-- ---------------------------------------------------------------------
-- Ejercicio 22. Demostrar que
--    (P ↔ Q) ↔ (Q ↔ P)
-- ----------------------------------------------------------------------

theorem iff.comm :
  (P ↔ Q) ↔ (Q ↔ P) :=
begin
  split,
  { apply iff.symm },
  { apply iff.symm },
end

-- ---------------------------------------------------------------------
-- Ejercicio 23. Demostrar que
--    (P ↔ Q) → (Q ↔ R) → (P ↔ R)
-- ----------------------------------------------------------------------

theorem iff.trans :
  (P ↔ Q) → (Q ↔ R) → (P ↔ R) :=
begin
  intros hPQ hQR,
  rw hPQ,
  exact hQR,
end

-- ---------------------------------------------------------------------
-- Ejercicio 24. Demostrar que
--    ¬(P ↔ ¬P)
-- ----------------------------------------------------------------------

theorem iff.boss :
  ¬(P ↔ ¬P) :=
begin
  rintro ⟨h1, h2⟩,
  have hnP : ¬P,
  { intro hP,
    exact h1 hP hP, },
  have hP : P := h2 hnP,
  exact hnP hP,
end

-------------------------------------------------------
-- § ↔ y ∧                                           --
-------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 25. Demostrar que
--    P ∧ Q ↔ Q ∧ P
-- ----------------------------------------------------------------------

-- 1ª demostración
theorem and.comm :
  P ∧ Q ↔ Q ∧ P :=
begin
  split;
  apply and.symm,
end

-- 2ª demostración
example :
  P ∧ Q ↔ Q ∧ P :=
⟨and.symm _ _, and.symm _ _⟩

-- ---------------------------------------------------------------------
-- Ejercicio 26. Demostrar que
--    ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R))
-- ----------------------------------------------------------------------

theorem and_assoc :
  ((P ∧ Q) ∧ R) ↔ (P ∧ (Q ∧ R)) :=
begin
  split,
  { rintro ⟨⟨hP, hQ⟩, hR⟩,
    exact ⟨hP, hQ, hR⟩ },
  { rintro ⟨hP, hQ, hR⟩,
    exact ⟨⟨hP, hQ⟩, hR⟩ },
end

-------------------------------------------------------
-- § Disyunción (∨)                                  --
-------------------------------------------------------

variable (S : Prop)

-- ---------------------------------------------------------------------
-- Ejercicio 27. Demostrar que
--    P → P ∨ Q
-- ----------------------------------------------------------------------

theorem or.intro_left :
  P → P ∨ Q :=
begin
  intro P,
  left,
  assumption,
end

-- ---------------------------------------------------------------------
-- Ejercicio 28. Demostrar que
--    Q → P ∨ Q
-- ----------------------------------------------------------------------

theorem or.intro_right :
  Q → P ∨ Q :=
begin
  intro Q,
  right,
  assumption,
end

-- ---------------------------------------------------------------------
-- Ejercicio 29. Demostrar que
--    P ∨ Q → (P → R) → (Q → R) → R
-- ----------------------------------------------------------------------

theorem or.elim :
  P ∨ Q → (P → R) → (Q → R) → R :=
begin
  intros hPoQ hPR hQR,
  cases hPoQ with hP hQ,
  { exact hPR hP },
  { exact hQR hQ },
end

-- ---------------------------------------------------------------------
-- Ejercicio 30. Demostrar que
--    P ∨ Q → Q ∨ P
-- ----------------------------------------------------------------------

theorem or.symm :
  P ∨ Q → Q ∨ P :=
begin
  intro hPoQ,
  cases hPoQ with hP hQ,
  { right, assumption },
  { left, assumption }
end

-- ---------------------------------------------------------------------
-- Ejercicio 31. Demostrar que
--    P ∨ Q ↔ Q ∨ P
-- ----------------------------------------------------------------------

theorem or.comm :
  P ∨ Q ↔ Q ∨ P :=
begin
  split;
  apply or.symm,
end

-- ---------------------------------------------------------------------
-- Ejercicio 32. Demostrar que
--    (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R)
-- ----------------------------------------------------------------------

theorem or.assoc :
  (P ∨ Q) ∨ R ↔ P ∨ (Q ∨ R) :=
begin
  split,
  { rintro ((hP | hQ) | hR),
    { left, assumption },
    { right, left, assumption },
    { right, right, assumption } },
  { rintro (hP | hQ | hR),
    { left, left, assumption },
    { left, right, assumption },
    { right, assumption } }
end

-------------------------------------------------------
-- § Más sobre → y and                               --
-------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 33. Demostrar que
--    (P → R) → (Q → S) → P ∨ Q → R ∨ S
-- ---------------------------------------------------------------------

theorem or.imp :
  (P → R) → (Q → S) → P ∨ Q → R ∨ S :=
begin
  rintro hPR hQS (hP | hQ),
  { left, exact hPR hP },
  { right, exact hQS hQ }
end

-- ---------------------------------------------------------------------
-- Ejercicio 34. Demostrar que
--    (P → Q) → P ∨ R → Q ∨ R
-- ----------------------------------------------------------------------

theorem or.imp_left :
  (P → Q) → P ∨ R → Q ∨ R :=
begin
  rintro hPQ (hP | hR),
  { left, exact hPQ hP },
  { right, assumption },
end

-- ---------------------------------------------------------------------
-- Ejercicio 35. Demostrar que
--    (P → Q) → R ∨ P → R ∨ Q
-- ----------------------------------------------------------------------

theorem or.imp_right :
  (P → Q) → R ∨ P → R ∨ Q :=
begin
  rw or.comm R,
  rw or.comm R,
  apply or.imp_left,
end

-- ---------------------------------------------------------------------
-- Ejercicio 36. Demostrar que
--    P ∨ Q ∨ R ↔ Q ∨ P ∨ R
-- ----------------------------------------------------------------------

theorem or.left_comm :
  P ∨ Q ∨ R ↔ Q ∨ P ∨ R :=
begin
  rw [or.comm P, or.assoc, or.comm R],
end

-- ---------------------------------------------------------------------
-- Ejercicio 37. Demostrar que
--    (P → R) → (Q → R) → P ∨ Q → R
-- ----------------------------------------------------------------------

theorem or.rec :
  (P → R) → (Q → R) → P ∨ Q → R :=
begin
  intros hPR hQR hPoQ,
  exact or.elim _ _ _ hPoQ hPR hQR,
end

-- ---------------------------------------------------------------------
-- Ejercicio 38. Demostrar que
--    (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S)
-- ----------------------------------------------------------------------

theorem or_congr :
  (P ↔ R) → (Q ↔ S) → (P ∨ Q ↔ R ∨ S) :=
begin
  rintro hPR hQS,
  rw [hPR, hQS],
end

-------------------------------------------------------
-- § true y false                                    --
-------------------------------------------------------

-- ---------------------------------------------------------------------
-- Ejercicio 39. Demostrar que
--    false → P
-- ----------------------------------------------------------------------

theorem false.elim :
  false → P :=
begin
  intro h,
  cases h,
end

-- ---------------------------------------------------------------------
-- Ejercicio 40. Demostrar que
--    P ∧ true ↔ P
-- ----------------------------------------------------------------------

theorem and_true_iff :
  P ∧ true ↔ P :=
begin
  split,
  { rintro ⟨hP, -⟩,
    exact hP },
  { intro hP,
    split,
    { exact hP },
    { trivial } }
end

-- ---------------------------------------------------------------------
-- Ejercicio 41. Demostrar que
--    P ∨ false ↔ P
-- ----------------------------------------------------------------------

theorem or_false_iff :
  P ∨ false ↔ P :=
begin
  split,
  { rintro (hP | h),
    { assumption },
    { cases h} },
  { intro hP,
    left,
    exact hP }
end

-- ---------------------------------------------------------------------
-- Ejercicio 42. Demostrar que
--    P ∨ Q → ¬P → Q
-- ----------------------------------------------------------------------

theorem or.resolve_left :
  P ∨ Q → ¬P → Q :=
begin
  rintro (hP | hQ) hnP,
  { apply false.elim,
    exact hnP hP },
  { exact hQ },
end

-- ---------------------------------------------------------------------
-- Ejercicio 43. Demostrar que
--    P ∨ Q ↔ ¬P → Q
-- ----------------------------------------------------------------------

theorem or_iff_not_imp_left :
  P ∨ Q ↔ ¬P → Q :=
begin
  split,
  { apply or.resolve_left },
  { intro hnPQ,
    by_cases h : P,
    { left, assumption },
    { right, exact hnPQ h} }
end

end oculto

-- =====================================================================
-- § Referencias                                                      --
-- =====================================================================

-- + Kevin Buzzard. "Formalising mathematics : workshop 1 — logic, sets,
--   functions, relations" https://bit.ly/3kJo231
-- + Kevin Buzzard. formalising-mathematics: Part_A_logic.lean
--   https://bit.ly/3m5n9kA
-- + Kevin Buzzard. formalising-mathematics: Part_A_logic_solutions.lean
--   https://bit.ly/3oaLwjv
