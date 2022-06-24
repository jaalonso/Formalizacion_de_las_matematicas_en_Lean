------------------------------------------------------------------------
-- Las relaciones de equivalencia son isomorfas a las particiones
------------------------------------------------------------------------

import tactic

-- =====================================================================
-- § Visión general                                                   --
-- =====================================================================

-- En esta teoría, definiremos las particiones de `A` y construiremos
-- algunas interfaz (es decir, probaremos algunas
-- proposiciones). Definiremos las clases de equivalencia y haremos lo
-- mismo. Finalmente, demostraremos que existe una biyección entre
-- relaciones de equivalencia en `A` y particiones de` A`.
--
-- En Lean se tiene las siguiente definiciones:
--    reflexive R := ∀ (x : A), R x x
--    symmetric R := ∀ ⦃x y : A⦄, R x y → R y x
--    transitive R := ∀ ⦃x y z : A⦄, R x y → R y z → R x z
--    equivalence R := reflexive R ∧ symmetric R ∧ transitive R
-- donde `A` un tipo y `R: A → A → Prop` es una relación binaria en `A`.

-- =====================================================================
-- § Particiones                                                      --
-- =====================================================================

-- =====================================================================
-- §§ Definición de una partición                                     --
-- =====================================================================

-- Sea `A` un tipo. Una partición en `A` es una estructura con los
-- siguientes  componentes:
-- 1) Un conjunto de subconjuntos de A. Dichos subconjuntos se llaman
--   los bloques de la partición.
-- 2) Una hipótesis (es decir, una prueba) de que los bloques no están vacíos.
-- 3) Una hipótesis de que cada término de tipo A está en uno de los bloques.
-- 4) Una hipótesis de que dos bloques con intersección no vacía son iguales.

-- ---------------------------------------------------------------------
-- Ejercicio 1. Definir la estructura `particion` tal que `particion A`
-- es el tipo de las particiones sobre `A`.
-- ---------------------------------------------------------------------

@[ext] structure particion (A : Type) :=
(Bloques    : set (set A))
(Hno_vacios : ∀ X ∈ Bloques, (X : set A).nonempty)
(Hrecubren  : ∀ a, ∃ X ∈ Bloques, a ∈ X)
(Hdisjuntos : ∀ X Y ∈ Bloques, (X ∩ Y : set A).nonempty → X = Y)

-- Notaciones
-- + `P : particion A` expresa que `P` es una partición de `A`.
-- + `Bloques P` es el conjunto de los bloque de P.
-- + `Hno_vacios P` prueba que los bloques de `P` son no vacíos.
-- + `Hrecubren P` prueba que los bloque de `P` recubren a `A`.
-- + `Hdisjuntos p` prueba que los bloques de `P` son disjuntos entre sí

-- ---------------------------------------------------------------------
-- Ejercicio 2. Abrir el espacio de nombre `particion`.
-- ---------------------------------------------------------------------

namespace particion

-- ---------------------------------------------------------------------
-- Ejercicio 3. Definir las siguientes variables
-- + A para un tipo
-- + P para las particiones sobre A
-- + X e Y para subconjuntos de A.
-- ---------------------------------------------------------------------

variable  {A : Type}
variable  {P : particion A}
variables {X Y : set A}

-- ---------------------------------------------------------------------
-- Ejercicio 4. Demostrar que si dos bloques de una partición tienen un
-- elemento en común, entonces son iguales.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
begin
  apply Hdisjuntos P,
  { exact hX, },
  { exact hY, },
  { rw set.nonempty_def,
    use a,
    split,
    { exact haX, },
    { exact haY, }},
end

-- 2ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
begin
  apply Hdisjuntos P,
  { exact hX, },
  { exact hY, },
  { use a,
    exact ⟨haX, haY⟩, },
end

-- 3ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
begin
  apply Hdisjuntos P,
  { exact hX, },
  { exact hY, },
  { exact ⟨a, haX, haY⟩, },
end

-- 4ª demostración
lemma iguales_si_comun
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  : X = Y :=
Hdisjuntos P X Y hX hY ⟨a, haX, haY⟩

-- ---------------------------------------------------------------------
-- Ejercicio 5. Demostrar que si dos bloques de una partición tienen
-- elementos comunes, entonces los elementos de uno también pertenecen
-- al otro.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
begin
  convert hbX,
  apply iguales_si_comun hY hX haY,
  exact haX,
end

-- 2ª demostración
example
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
begin
  have hXY : X = Y := iguales_si_comun hX hY haX haY,
  rw ← hXY,
  exact hbX,
end

-- 3ª demostración
lemma pertenece_si_pertenece
  (hX : X ∈ Bloques P)
  (hY : Y ∈ Bloques P)
  {a b : A}
  (haX : a ∈ X)
  (haY : a ∈ Y)
  (hbX : b ∈ X)
  : b ∈ Y :=
begin
  convert hbX,
  exact iguales_si_comun hY hX haY haX,
end

-- ---------------------------------------------------------------------
-- Ejercicio 6. Demostrar que si P es una partición sobre A, entonces
-- para cada elemento a de A hay algún bloque X de P tal que a ∈ X.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (a : A)
  : ∃ X, X ∈ Bloques P ∧ a ∈ X :=
begin
  rcases Hrecubren P a with ⟨X, hX, haX⟩,
  use X,
  exact ⟨hX, haX⟩,
end

-- 2ª demostración
example
  (a : A)
  : ∃ X, X ∈ Bloques P ∧ a ∈ X :=
begin
  rcases Hrecubren P a with ⟨X, hX, haX⟩,
  exact ⟨X, hX, haX⟩,
end

-- 3ª demostración
lemma pertenece_bloque
  (a : A)
  : ∃ X : set A, X ∈ Bloques P ∧ a ∈ X :=
begin
  obtain ⟨X, hX, haX⟩ := Hrecubren P a,
  use X,
  exact ⟨hX, haX⟩,
end

-- ---------------------------------------------------------------------
-- Ejercicio 7. Cerrar el espacio de nombres `particion`.
-- ---------------------------------------------------------------------

end particion

-- =====================================================================
-- § Relaciones de equivalencia                                      --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio 8. Abrir la sección `clases_de_equivalencia`.
-- ---------------------------------------------------------------------

section clases_de_equivalencia

-- =====================================================================
-- §§ Definición de relaciones de equivalencia                        --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio 9. Definir las siguientes variables
-- + A para un tipo
-- + R para las relaciones binarias en A.
-- ---------------------------------------------------------------------

variable {A : Type}
variable (R : A → A → Prop)

-- ---------------------------------------------------------------------
-- Ejercicio 10. Definir la función
--    clase : A → set A
-- tal que (clase a) es el conjunto de los elementos relacionados con a
-- (mediante R). Se dice que `clase a` es la clase de a.
-- ---------------------------------------------------------------------

def clase (a : A) :=
  {b : A | R b a}

-- =====================================================================
-- § Lemas elementales de las clases                   --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio 11. Demostrar que
--    b ∈ clase R a ↔ R b a
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
begin
  unfold clase,
  dsimp,
  refl,
end

-- 2ª demostración
lemma pertenece_clase_syss
  {a b : A}
  : b ∈ clase R a ↔ R b a :=
by refl

-- ---------------------------------------------------------------------
-- Ejercicio 12. Definir como hipótesis hR el que R es una relación de
-- equivalencia y usarla en el resto de la sección.
-- ---------------------------------------------------------------------

variables {R} (hR : equivalence R)
include hR

-- ---------------------------------------------------------------------
-- Ejercicio 13. Demostrar que
--    a ∈ clase R a
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  suffices h : reflexive R,
  { exact h a, },
  { rcases hR with ⟨h2, -, -⟩,
    exact h2, },
end

-- 2ª demostración
example
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  suffices h : reflexive R,
  { exact h a, },
  { exact hR.1, },
end

-- 3ª demostración
example
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  rcases hR with ⟨hrefl, -, -⟩,
  exact hrefl a,
end

-- 4ª demostración
example
  (a : A)
  : a ∈ clase R a :=
begin
  obtain ⟨hrefl, -, -⟩ := hR,
  rw pertenece_clase_syss,
  apply hrefl,
end

-- 5ª demostración
example
  (a : A)
  : a ∈ clase R a :=
begin
  rw pertenece_clase_syss,
  apply hR.1,
end

-- 6ª demostración
lemma pertenece_clase_propia
  (a : A)
  : a ∈ clase R a :=
(pertenece_clase_syss R).mpr (hR.1 a)

-- ---------------------------------------------------------------------
-- Ejercicio 14. Demostrar que
--    a ∈ clase R b → clase R a ⊆ clase R b
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
begin
  intro hab,
  intros z hza,
  rw pertenece_clase_syss at hab hza ⊢,
  obtain ⟨-, -, htrans⟩ := hR,
  exact htrans hza hab,
end

-- 2ª demostración
example
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
begin
  intros hab z hza,
  exact hR.2.2 hza hab,
end

-- 3ª demostración
lemma subclase_si_pertenece
  {a b : A}
  : a ∈ clase R b → clase R a ⊆ clase R b :=
λ hab z hza, hR.2.2 hza hab

-- ---------------------------------------------------------------------
-- Ejercicio 15. Demostrar que
--    a ∈ clase R b → clase R a = clase R b
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
begin
  intro hab,
  apply set.subset.antisymm,
  { apply subclase_si_pertenece hR hab, },
  { apply subclase_si_pertenece hR,
    rcases hR with ⟨-, hsymm, -⟩,
    exact hsymm hab }
end

-- 2ª demostración
example
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
begin
  intro hab,
  apply set.subset.antisymm,
  { exact subclase_si_pertenece hR hab, },
  { exact subclase_si_pertenece hR (hR.2.1 hab), }
end

-- 3ª demostración
example
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
begin
  intro hab,
  exact set.subset.antisymm
         (subclase_si_pertenece hR hab)
         (subclase_si_pertenece hR (hR.2.1 hab))
end

-- 4ª demostración
lemma clases_iguales_si_pertenece
  {a b : A}
  : a ∈ clase R b → clase R a = clase R b :=
λ hab, set.subset.antisymm
        (subclase_si_pertenece hR hab)
        (subclase_si_pertenece hR (hR.2.1 hab))

-- ---------------------------------------------------------------------
-- Ejercicio 16. Cerrar la sección `clases_de_equivalencia`.
-- ---------------------------------------------------------------------

end clases_de_equivalencia

-- =====================================================================
-- § El teorema                                                       --
-- =====================================================================

-- Sea `A` un tipo. Existe una biyección entre las relaciones de
-- equivalencia en `A` y particiones de `A`. Lo demostraremos
-- escribiendo una dfunción en cada dirección y probando que las
-- funciones son inversas.

-- ---------------------------------------------------------------------
-- Ejercicio 17. Abrir el espacio de nombre `particion`.
-- ---------------------------------------------------------------------

open particion

-- ---------------------------------------------------------------------
-- Ejercicio 18. Definir las variables
-- + A para tipos y
-- + R para relaciones binarias en A.
-- ---------------------------------------------------------------------

variable {A : Type}
variable (R : A → A → Prop)

-- ---------------------------------------------------------------------
-- Ejercicio 19. Definir la función
--    clases : (A → A → Prop) → set (set A)
-- tal que (clases R) es el conjunto de las clases de R.
-- ---------------------------------------------------------------------

def clases : (A → A → Prop) → set (set A) :=
  λ R, {B : set A | ∃ x : A, B = clase R x}

-- ---------------------------------------------------------------------
-- Ejercicio 20. Demostrar que si R es una relación de equivalencia,
-- entonces las clases de R son no vacías.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (hR: equivalence R)
  : ∀ (X : set A), X ∈ clases R → X.nonempty :=
begin
  intros X hX,
  unfold clases at hX,
  dsimp at hX,
  cases hX with a ha,
  rw ha,
  rw set.nonempty_def,
  use a,
  rw pertenece_clase_syss,
  rcases hR with ⟨hrefl, -, -⟩,
  exact hrefl a,
end

-- 2ª demostración
lemma clases_no_vacias
  (hR: equivalence R)
  : ∀ (X : set A), X ∈ clases R → X.nonempty :=
begin
  rintros _ ⟨a, rfl⟩,
  use a,
  rw pertenece_clase_syss,
  apply hR.1,
end

-- ---------------------------------------------------------------------
-- Ejercicio 21. Demostrar que si R es una relación de equivalencia en A,
-- entonces las clases de R recubren a A; es decir, para cada elemento a
-- de A existe una clase X de R tal que a ∈ X.
-- ---------------------------------------------------------------------

-- 1ª demostración,
example
  (hR: equivalence R)
  : ∀ a, ∃ X ∈ clases R, a ∈ X :=
begin
  intro a,
  use clase R a,
  split,
  { unfold clases,
    dsimp,
    use a, },
  { exact pertenece_clase_propia hR a, },
end

-- 2ª demostración,
lemma clases_recubren
  (hR: equivalence R)
  : ∀ a, ∃ X ∈ clases R, a ∈ X :=
begin
  intro a,
  use clase R a,
  split,
  { use a, },
  { exact hR.1 a, },
end

-- ---------------------------------------------------------------------
-- Ejercicio 22. Demostrar que si R es una relación de equivalencia,
-- entonces las clases de R son disjuntas; es decir, si dos clases de R
-- son no disjuntas, entonces son iguales.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  intros X Y hX hY hXY,
  unfold clases at hX hY,
  dsimp at hX hY,
  cases hX with a ha,
  cases hY with b hb,
  rw [ha, hb] at *,
  rw set.nonempty_def at hXY,
  cases hXY with c hc,
  cases hc with hca hcb,
  apply clases_iguales_si_pertenece hR,
  apply hR.2.2 _ hcb,
  apply hR.2.1,
  exact hca,
end

-- 2ª demostración
example
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  intros X Y hX hY hXY,
  cases hX with a ha,
  cases hY with b hb,
  rw [ha, hb] at *,
  rw set.nonempty_def at hXY,
  cases hXY with c hc,
  cases hc with hca hcb,
  apply clases_iguales_si_pertenece hR,
  apply hR.2.2 _ hcb,
  apply hR.2.1,
  exact hca,
end

-- 3ª demostración
example
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
  apply clases_iguales_si_pertenece hR,
  apply hR.2.2 _ hcb,
  apply hR.2.1,
  exact hca,
end

-- 4ª demostración
lemma clases_disjuntas
  (hR: equivalence R)
  : ∀ X Y ∈ clases R, (X ∩ Y : set A).nonempty → X = Y :=
begin
  rintros X Y ⟨a, rfl⟩ ⟨b, rfl⟩ ⟨c, hca, hcb⟩,
  exact clases_iguales_si_pertenece hR (hR.2.2 (hR.2.1 hca) hcb),
end

-- ---------------------------------------------------------------------
-- Ejercicio 23. Definir la función
--    cociente : {R : A → A → Prop // equivalence R} → particion A
-- tal que (cociente R) es el conjunto cociente  de la relación de
-- equivalencia R.
-- ---------------------------------------------------------------------

def cociente : {R : A → A → Prop // equivalence R} → particion A :=
  λ R, { Bloques    := {B : set A | ∃ x : A, B = clase R.1 x},
         Hno_vacios := clases_no_vacias R.1 R.2,
         Hrecubren  := clases_recubren R.1 R.2,
         Hdisjuntos := clases_disjuntas R.1 R.2, }

-- ---------------------------------------------------------------------
-- Ejercicio 24. Definir P como una variable sobre los conjuntos de
-- conjuntos de A.
-- ---------------------------------------------------------------------

variable (P : set (set A))

-- ---------------------------------------------------------------------
-- Ejercicio 25. Definir la función
--    relacion : (particion A) → (A → A → Prop)
-- tal que (relacion P) es la relación correspondiente a la partición P.
-- ---------------------------------------------------------------------

def relacion : (particion A) → (A → A → Prop) :=
  λ P a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X

-- ---------------------------------------------------------------------
-- Ejercicio 26. Demostrar que la relación correspondiente a la
-- partición P es reflexiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (P : particion A)
  : reflexive (relacion P) :=
begin
  rw reflexive,
  intro a,
  unfold relacion,
  intros X hXC haX,
  exact haX,
end

-- 2ª demostración
example
  (P : particion A)
  : reflexive (relacion P) :=
begin
  intro a,
  intros X hXC haX,
  exact haX,
end

-- 3ª demostración
example
  (P : particion A)
  : reflexive (relacion P) :=
begin
  intros a X hXC haX,
  exact haX,
end

-- 4ª demostración
lemma reflexiva
  (P : particion A)
  : reflexive (relacion P) :=
λ a X hXC haX, haX

-- ---------------------------------------------------------------------
-- Ejercicio 37. Demostrar que la relación correspondiente a la parición
-- P es simétrica
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (P : particion A)
  : symmetric (relacion P) :=
begin
  rw symmetric,
  intros a b hab,
  unfold relacion at *,
  intros X hX hbX,
  obtain ⟨Y, hY, haY⟩ := Hrecubren P a,
  specialize hab Y hY haY,
  exact pertenece_si_pertenece hY hX hab hbX haY,
end

-- 2ª demostración
example
  (P : particion A)
  : symmetric (relacion P) :=
begin
  intros a b hab,
  intros X hX hbX,
  obtain ⟨Y, hY, haY⟩ := Hrecubren P a,
  specialize hab Y hY haY,
  exact pertenece_si_pertenece hY hX hab hbX haY,
end

-- 3ª demostración
lemma simetrica
  (P : particion A)
  : symmetric (relacion P) :=
begin
  intros a b h X hX hbX,
  obtain ⟨Y, hY, haY⟩ := Hrecubren P a,
  specialize h Y hY haY,
  exact pertenece_si_pertenece hY hX h hbX haY,
end

-- ---------------------------------------------------------------------
-- Ejercicio 28. Demostrar que la relación correspondiente a la relación P
-- es transitiva.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (P : particion A)
  : transitive (relacion P) :=
begin
  unfold transitive,
  intros a b c hab hbc,
  unfold relacion at *,
  intros X hX haX,
  apply hbc,
  { exact hX, },
  { apply hab,
    { exact hX, },
    { exact haX, }},
end

-- 2ª demostración
example
  (P : particion A)
  : transitive (relacion P) :=
begin
  intros a b c hab hbc,
  intros X hX haX,
  apply hbc X hX,
  apply hab X hX,
  exact haX,
end

-- 3ª demostración
example
  (P : particion A)
  : transitive (relacion P) :=
begin
  intros a b c hab hbc X hX haX,
  exact hbc X hX (hab X hX haX),
end

-- 4ª demostración
lemma transitiva
  (P : particion A)
  : transitive (relacion P) :=
λ a b c hab hbc X hX haX, hbc X hX (hab X hX haX)

-- ---------------------------------------------------------------------
-- Ejercicio 29. Definir la función
--    relacionP : particion A → {R : A → A → Prop // equivalence R}
-- ---------------------------------------------------------------------

def relacionP : particion A → {R : A → A → Prop // equivalence R} :=
  λ P, ⟨λ a b, ∀ X ∈ Bloques P, a ∈ X → b ∈ X,
        ⟨reflexiva P, simetrica P, transitiva P⟩⟩

-- ---------------------------------------------------------------------
-- Ejercicio 30. Demostrar que relacionP es inversa por la izquierda de
-- cociente.
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  unfold function.left_inverse,
  intro S,
  cases S with R hR,
  unfold relacionP cociente relacion,
  simp,
  ext a b,
  split,
  { intros hab,
    apply hR.2.1,
    unfold clase at hab,
    dsimp at hab,
    apply hab,
    apply hR.1, },
  { intros hab c hac,
    unfold clase at *,
    dsimp at *,
    apply hR.2.2 (hR.2.1 hab) hac, },
end

-- 2ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  split,
  { intros hab,
    apply hR.2.1,
    apply hab,
    apply hR.1, },
  { intros hab c hac,
    apply hR.2.2 (hR.2.1 hab) hac, },
end

-- 3ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  split,
  { intros hab,
    exact hR.2.1 (hab a (hR.1 a)), },
  { intros hab c hac,
    exact hR.2.2 (hR.2.1 hab) hac, },
end

-- 4ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  split,
  { exact λ hab, hR.2.1 (hab a (hR.1 a)), },
  { exact λ hab c hac, hR.2.2 (hR.2.1 hab) hac, },
end

-- 5ª demostración
example :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  simp [relacionP, cociente],
  ext a b,
  exact ⟨λ hab, hR.2.1 (hab a (hR.1 a)),
         λ hab c hac, hR.2.2 (hR.2.1 hab) hac⟩,
end

-- 6ª demostración
lemma inversa_izq :
  function.left_inverse relacionP (@cociente A) :=
begin
  rintro ⟨R, hR⟩,
  suffices : (λ (a b : A), ∀ (c : A), a ∈ clase R c → b ∈ clase R c) = R,
  { simpa [relacionP, cociente], },
  { ext a b,
    show (∀ (c : A), a ∈ clase R c → b ∈ clase R c) ↔ R a b,
    split,
    { intros hab,
      apply hR.2.1,
      unfold clase at hab,
      dsimp at hab,
      apply hab,
      apply hR.1, },
    { intros hab c hac,
      unfold clase at *,
      dsimp at *,
      apply hR.2.2 (hR.2.1 hab) hac, }},
end

-- ---------------------------------------------------------------------
-- Ejercicio 31. Demostrar que la función cociente que aplica relaciones
-- de equivalencia en la partición del conjunto cociente es inyectiva.
-- ---------------------------------------------------------------------

lemma cociente_es_inyectiva :
  function.injective (@cociente A) :=
function.left_inverse.injective inversa_izq

-- ---------------------------------------------------------------------
-- Ejercicio 32. Demostrar que relacionP es inversa por la derecha de
-- cociente.
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  function.right_inverse relacionP (@cociente A) :=
begin
  unfold function.right_inverse,
  unfold function.left_inverse,
  intro P,
  ext X,
  simp [cociente],
  split,
  { intro h,
    cases h with a ha,
    rw ha,
    rcases Hrecubren P a with ⟨X, hX, haX⟩,
    convert hX,
    ext b,
    rw pertenece_clase_syss,
    split,
    { intro hba,
      rcases Hrecubren P b with ⟨Y, hY, hbY⟩,
      specialize hba Y hY hbY,
      convert hbY,
      exact iguales_si_comun hX hY haX hba, },
    { intros hbX Y hY hbY,
      apply pertenece_si_pertenece hX hY hbX hbY haX, }},
  { intro hX,
    rcases Hno_vacios P X hX with ⟨a, ha⟩,
    use a,
    ext b,
    split,
    { intro hbX,
      rw pertenece_clase_syss,
      intros Y hY hbY,
      exact pertenece_si_pertenece hX hY hbX hbY ha, },
    { rw pertenece_clase_syss,
      intro hba,
      rcases Hrecubren P b with ⟨Y, hY, hbY⟩,
      specialize hba Y hY hbY,
      exact pertenece_si_pertenece hY hX hba ha hbY, }}
end

-- 2ª demostración
lemma inversa_dcha :
  function.right_inverse relacionP (@cociente A) :=
begin
  intro P,
  ext X,
  show (∃ (a : A), X = clase _ a) ↔ X ∈ Bloques P,
  split,
  { rintro ⟨a, rfl⟩,
    obtain ⟨X, hX, haX⟩ := Hrecubren P a,
    convert hX,
    ext b,
    rw pertenece_clase_syss,
    split,
    { intro hba,
      obtain ⟨Y, hY, hbY⟩ := Hrecubren P b,
      specialize hba Y hY hbY,
      convert hbY,
      exact iguales_si_comun hX hY haX hba, },
    { intros hbX Y hY hbY,
      apply pertenece_si_pertenece hX hY hbX hbY haX, }},
  { intro hX,
    rcases Hno_vacios P X hX with ⟨a, ha⟩,
    use a,
    ext b,
    split,
    { intro hbX,
      rw pertenece_clase_syss,
      intros Y hY hbY,
      exact pertenece_si_pertenece hX hY hbX hbY ha, },
    { rw pertenece_clase_syss,
      intro hba,
      obtain ⟨Y, hY, hbY⟩ := Hrecubren P b,
      specialize hba Y hY hbY,
      exact pertenece_si_pertenece hY hX hba ha hbY, }}
end

-- ---------------------------------------------------------------------
-- Ejercicio 33. Demostrar que la función cociente que aplica relaciones
-- de equivalencia en la partición del conjunto cociente es suprayectiva.
-- ---------------------------------------------------------------------

lemma cociente_es_suprayectiva :
  function.surjective (@cociente A) :=
function.right_inverse.surjective inversa_dcha

-- ---------------------------------------------------------------------
-- Ejercicio 34. Demostrar que la función cociente que aplica relaciones
-- de equivalencia en la partición del conjunto cociente es biyectiva.
-- ---------------------------------------------------------------------

lemma cociente_es_biyectiva :
  function.bijective (@cociente A) :=
⟨cociente_es_inyectiva, cociente_es_suprayectiva⟩

-- ---------------------------------------------------------------------
-- Ejercicio 35. Demostrar que los tipos de las relaciones de equivalencia
-- sobre A y el de las particiones de A son isomorfos.
-- ---------------------------------------------------------------------

theorem equivalencia_particiones
  (A : Type)
  : {R : A → A → Prop // equivalence R} ≃ particion A :=
{ to_fun    := cociente,
  inv_fun   := relacionP,
  left_inv  := inversa_izq,
  right_inv := inversa_dcha, }

-- =====================================================================
-- § Referencias                                                      --
-- =====================================================================

-- + Kevin Buzzard. "Formalising mathematics : workshop 1 — logic, sets,
--   functions, relations" https://bit.ly/3kJo231
-- + Kevin Buzzard. formalising-mathematics: Part_D_relations.lean
--   https://bit.ly/3AQWY7o
-- + Kevin Buzzard. formalising-mathematics: Part_D_relations_solutions.lean
--   https://bit.ly/2WpcfgY
