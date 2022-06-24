-- ---------------------------------------------------------------------
-- Ejercicio. Importar las siguientes librerías
-- + tactic (con las tácticas)
-- + data.set.basic (con la teoría básica de conjuntos)
-- + data.set.lattice (con las uniones e intersecciones infinitas).
-- ---------------------------------------------------------------------

import tactic
import data.set.basic
import data.set.lattice

-- =====================================================================
-- § Introducción                                                     --
-- =====================================================================

-- Nota. Si `X` es un tipo, entonces `set X` es el tipo de los
-- subconjuntos de `X`.

-- Nota. Si `X` es un tipo, entonces
-- + `a : X`  significa que `a` es un término de tipo `X`
-- + `S : set X`  significa que `S` es un conjunto de términos de tipo `X`.

-- Nota: Si `S : set X` y `a : X`, entonces existe un predicado `a ∈ S`
-- que significa que `a` pertenece al subconjunto `S` de `X`.

-- =====================================================================
-- § Implementaciones                                                 --
-- =====================================================================

-- Nota: Si `S : set X`, entonces `S` es una función de `X` a `Prop`. La
-- idea es que un subconjunto `S` de `X` se representa como una función a
-- `{true, false}` que aplica los elementos de `S` a `true` y los
-- restantes a `false`.

-- Nota: La definición del tipo de los subconjuntos es `set X := X → Prop`

-- Nota: Si `S : set X`, entonces `a ∈ S` significa `S a`.

-- =====================================================================
-- § Notación                                                         --
-- =====================================================================

-- Nota: En lo que sigue, `X` e `Y` son tipos.

-- Nota: Cada tipo tiene un conjunto vacío denotado por `∅ : set X`

-- Nota: Cada tipo tiene un conjunto universal denotado por
-- `set.univ : set X` (o simplemente `univ : set X` si previamente se ha
-- escrito `open set`).

-- Nota: Si `S : set X` entonces su complementario es `Sᶜ : set X`.

-- Nota: En lo que sigue, `f : X → Y`.

-- Nota: Si `S : set X`, entonces `f '' S : set Y` es la imagen de `S`
-- por `f`.

-- Nota: Si `T : set Y`, entonces `f ⁻¹' T : set X` es la preimagen de
-- `T` por `f`.

-- Nota: El rango de f es `range f` (que es igual a `f '' univ`).

-- Nota: La definición de subconjunto es:
--    subset_def : S ⊆ T ↔ ∀ x, x ∈ S → x ∈ T

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar las siguientes variables:
-- + X, Y, Z sobre tipos.
-- + f sobre funciones de X en Y.
-- + g sobre funciones de Y en Z.
-- + S sobre el tipo de subconjuntos de X.
-- + T sobre el tipo de subconjuntos de Z.
-- + y sobre elementos de Y.
-- ---------------------------------------------------------------------

variables (X Y Z : Type)
variable  (f : X → Y)
variable  (g : Y → Z)
variable  (S : set X)
variable  (T : set Z)
variable  (y : Y)

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre set (de los conjuntos).
-- ---------------------------------------------------------------------

open set

-- =====================================================================
-- § Imagen                                                           --
-- =====================================================================

-- Nota. La imagen de un conjunto mediante una función está definida en
-- pfun.lean por
--    image_def (s : set α) :
--      image f s = {y | ∃ x ∈ s, y ∈ f x}

-- Nota. La imagen, mediante f, de S se representa por
--    f '' S

-- Nota. la pertenencia a la imagen está caracterizada en basic.lean por
--    mem_image (f : α → β) (s : set α) (y : β) :
--      y ∈ f '' s ↔ ∃ x, x ∈ s ∧ f x = y

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la imagen de cualquier conjunto S por la
-- función identidad es S.
-- ---------------------------------------------------------------------

-- 1ª demostración
lemma image_identity :
  id '' S = S :=
begin
  ext x,
  split,
  { intro h,
    rw mem_image at h,
    cases h with y hy,
    cases hy with hyS hid,
    rw id.def at hid,
    rw ← hid,
    exact hyS },
  { intro hxS,
    rw mem_image,
    use x,
    split,
    { exact hxS, },
    { rw id.def, } }
end

-- 2ª demostración
example :
  id '' S = S :=
begin
  ext x,
  split,
  { intro h,
    rcases h with ⟨y, hyS, hid⟩,
    rw ← hid,
    exact hyS, },
  { intro hxS,
    use x,
    use hxS,
    refl, }
end

-- 3ª demostración
example :
  id '' S = S :=
begin
  ext x,
  split,
  { rintro ⟨y, hyS, hid⟩,
    rw ← hid,
    exact hyS, },
  { intro hxS,
    use [x, hxS],
    refl, }
end

-- 4ª demostración
example :
  id '' S = S :=
begin
  ext x,
  split,
  { rintro ⟨y, hyS, rfl⟩,
    exact hyS, },
  { intro hxS,
    exact ⟨x, hxS, rfl⟩ },
end

-- 5ª demostración
example :
  id '' S = S :=
-- by library_search [- image_identity]
image_id S

-- 6ª demostración
example :
  id '' S = S :=
by simp

-- 7ª demostración
example :
  id '' S = S :=
by finish

-- 8ª demostración
example :
  id '' S = S :=
by tidy

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (g ∘ f) '' S = g '' (f '' S)
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z,
  split,
  { intro h,
    rw mem_image at *,
    cases h with x hx,
    use f x,
    split,
    { rw mem_image,
      use x,
      split,
      { exact hx.left, },
      { refl, } },
    { exact hx.right, }},
  { intro h,
    rw mem_image at *,
    cases h with x hx,
    rw mem_image at hx,
    cases hx.left with a ha,
    use a,
    split,
    { exact ha.left, },
    { dsimp,
      rw ha.2,
      rw hx.2, }},
end

-- 2ª demostración
example :
  (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z,
  split,
  { intro h,
    rw mem_image at *,
    rcases h with ⟨x, hxS, h_gfx⟩,
    use f x,
    split,
    { rw mem_image,
      use x,
      use hxS,},
    { exact h_gfx, }},
  { intro h,
    rw mem_image at *,
    rcases h with ⟨x, hxf, hxg⟩,
    rw mem_image at hxf,
    rcases hxf with ⟨a, haS, haf⟩,
    use a,
    split,
    { exact haS, },
    { dsimp,
      rw haf,
      exact hxg, }},
end

-- 3ª demostración
example :
  (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z,
  split,
  { intro h,
    rcases h with ⟨x, hxS, h_gfx⟩,
    use f x,
    split,
    { use x,
      use hxS,},
    { exact h_gfx, }},
  { intro h,
    rcases h with ⟨x, hxf, hxg⟩,
    rcases hxf with ⟨a, haS, haf⟩,
    use a,
    split,
    { exact haS, },
    { dsimp,
      rw haf,
      exact hxg, }},
end

-- 4ª demostración
example :
  (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z,
  split,
  { intro h,
    rcases h with ⟨x, hxS, h_gfx⟩,
    use f x,
    split,
    { use [x, hxS],},
    { exact h_gfx, }},
  { intro h,
    rcases h with ⟨x, hxf, hxg⟩,
    rcases hxf with ⟨a, haS, haf⟩,
    use a,
    split,
    { exact haS, },
    { dsimp,
      rw haf,
      exact hxg, }},
end

-- 5ª demostración
example :
  (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z,
  split,
  { intro h,
    rcases h with ⟨x, hxS, h_gfx⟩,
    use f x,
    { use [x, hxS, h_gfx], }},
  { intro h,
    rcases h with ⟨x, hxf, hxg⟩,
    rcases hxf with ⟨a, haS, haf⟩,
    use a,
    split,
    { exact haS, },
    { dsimp,
      rw haf,
      exact hxg, }},
end

-- 6ª demostración
example :
  (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z,
  split,
  { intro h,
    rcases h with ⟨x, hxS, h_gfx⟩,
    use [f x, x, hxS, h_gfx], },
  { intro h,
    rcases h with ⟨x, hxf, hxg⟩,
    rcases hxf with ⟨a, haS, haf⟩,
    use a,
    split,
    { exact haS, },
    { dsimp,
      rw haf,
      exact hxg, }},
end

-- 7ª demostración
lemma image_comp :
  (g ∘ f) '' S = g '' (f '' S) :=
begin
  ext z,
  split,
  { rintro ⟨x, hxS, h_gfx⟩,
    use [f x, x, hxS, h_gfx] },
  { rintro ⟨y, ⟨x, hxS, rfl⟩, rfl⟩,
    exact ⟨x, hxS, rfl⟩ }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre function (de las funciones).
-- ---------------------------------------------------------------------

open function

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva, entonces la función que
-- le asigna a cada conjunto su imagen por f también es inyectiva.
-- ---------------------------------------------------------------------

lemma image_injective :
  injective f → injective (λ S, f '' S) :=
begin
  intro hf,
  intros S T h,
  dsimp at h,
  ext x,
  suffices : ∀ S T : set X, f '' S = f '' T → x ∈ S → x ∈ T,
  { split,
    { apply this _ _ h, },
    { apply this _ _ h.symm, }},
  { clear h S T,
    intros S T h hxS,
    have hfx : f x ∈ f '' T,
    { rw ← h,
      use [x, hxS] },
    { rcases hfx with ⟨y, hyT, hfy⟩,
      convert hyT,
      apply hf,
      exact hfy.symm, }},
end

-- =====================================================================
-- § Imagen inversa                                                   --
-- =====================================================================

-- Nota. La imagen de un conjunto mediante una función está definida en
-- pfun.lean por
--    preimage_def (s : set β) :
--      preimage f s = {x | ∃ y ∈ s, y ∈ f x}

-- Nota. La imagen inversa, mediante f, de S se representa por
--    f ⁻¹' S

-- Nota. La pertenencia a la imagen está caracterizada en basic.lean por
--    mem_preimage {s : set β} {a : α} :
--      (a ∈ f ⁻¹' s) ↔ (f a ∈ s)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la imagen inversa de cualquier conjunto por
-- la identidad es él mismo.
-- ---------------------------------------------------------------------

example :
  S = id ⁻¹' S :=
begin
  refl,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (g ∘ f) ⁻¹' T = f ⁻¹' (g ⁻¹' T)
-- ---------------------------------------------------------------------

example :
  (g ∘ f) ⁻¹' T = f ⁻¹' (g ⁻¹' T) :=
begin
  refl,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es suprayectiva, entonces la función
-- que asigna a cada conjunto su imagen inversa por f es inyectiva.
-- ---------------------------------------------------------------------

lemma preimage_injective
  (hf : surjective f)
  : injective (λ T, f ⁻¹' T) :=
begin
  intros T U h,
  ext y,
  suffices : ∀ {T U}, f ⁻¹' T = f ⁻¹' U → y ∈ T → y ∈ U,
  { exact ⟨this h, this h.symm⟩ },
  { intros T U h hyT,
    rcases hf y with ⟨x, rfl⟩,
    rwa [← mem_preimage, ← h], },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es suprayectiva, entonces la función
-- que le asigna a cada conjunto su imagen por f es suprayectiva.
-- ---------------------------------------------------------------------

lemma image_surjective
  (hf : surjective f)
  : surjective (λ S, f '' S) :=
begin
  intro T,
  use f ⁻¹' T,
  dsimp only,
  ext y,
  split,
  { rintro ⟨x, hx, rfl⟩,
    exact hx },
  { intro hyT,
    rcases hf y with ⟨x, rfl⟩,
    use [x, hyT] }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si f es inyectiva, entonces la función que a
-- cada conjunto le asigna su imagen inversa por S es suprayectiva.


lemma preimage_surjective
  (hf : injective f)
  : surjective (λ S, f ⁻¹' S) :=
begin
  intro S,
  use f '' S,
  ext x,
  split,
  { rintro ⟨y, hyS, h⟩,
    rwa ← (hf h) },
  { intro h,
    use [x, h, rfl] }
end

-- =====================================================================
-- § Unión general                                                    --
-- =====================================================================

-- Nota. La unión de una familia de conjuntos está definida (en
-- lattice.lean) como su supremo
--    def Union (s : ι → set β) : set β := supr s

-- Nota. Sea `(ι : Type)` y `(F : ι → set X)`, la unión de la familia de
-- conjuntos `F` se representa por `⋃ (i : ι), F i`.

-- Nota. La caracterización de la pertenencia a la unión de una familia
-- es
--    mem_Union {x : β} {s : ι → set β} :
--       x ∈ Union s ↔ ∃ i, x ∈ s i
-- o bien
--    mem_Union {x : β} {F : ι → set β} :
--       (x ∈ ⋃ (i : ι), F i) ↔ ∃ j : ι, x ∈ F j

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar
-- + ι una variable sobre tipos
-- + F una variable para las familias de subconjuntos de X con índice ι
-- + x una varible sobre términos de tipo X.
-- ---------------------------------------------------------------------

variable (ι : Type)
variable (F : ι → set X)
variable (x : X)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la imagen de la unión de una familia es
-- igual a la unión de las imágenes de cada elemento de la familia.
-- ---------------------------------------------------------------------

lemma image_Union  :
  f '' (⋃ (i : ι), F i) = ⋃ (i : ι), f '' (F i) :=
begin
  ext y,
  split,
  { rintro ⟨x, hxF, rfl⟩,
    rw mem_Union at *,
    cases hxF with i hi,
    use [i, x, hi] },
  { intro h,
    rw mem_Union at h,
    rcases h with ⟨i, x, hxi, rfl⟩,
    use x,
    rw mem_Union,
    use i,
    assumption }
end

-- =====================================================================
-- § Unión general acotada                                            --
-- =====================================================================

-- Nota. Si `F : ι → set X` y `J : set ι`, entonces `⋃ (i ∈ J), F i` es
-- la unión general acotada y sus elementos se caracterizan por
--    mem_bUnion_iff : (x ∈ ⋃ (i ∈ J), F i) ↔ ∃ (j ∈ J), x ∈ F j

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' (⋃ (i ∈ Z), F i) = ⋃ (i ∈ Z), f ⁻¹' (F i)
-- ---------------------------------------------------------------------

lemma preimage_bUnion
  (F : ι → set Y)
  (Z : set ι)
  : f ⁻¹' (⋃ (i ∈ Z), F i) = ⋃ (i ∈ Z), f ⁻¹' (F i) :=
begin
  ext y,
  rw [mem_preimage, mem_bUnion_iff, mem_bUnion_iff],
  refl,
end
