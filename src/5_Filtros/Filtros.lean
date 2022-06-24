-- Filtros

-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de filtros.
-- ---------------------------------------------------------------------

import order.filter.basic

-- =====================================================================
-- § Introducción                                                     --
-- =====================================================================

-- Un espacio topológico sobre un tipo `α` es una colección de
-- subconjuntos de `α` (los conjuntos abiertos) que satisfacen algunos
-- axiomas. Un filtro es un tipo similar: es una colección de
-- subconjuntos de `α` que satisfacen otros axiomas.
--
-- Antes de ver la definición formal, empecemos por la idea. Un filtro
-- en `α` es una generalización muy potente del concepto de subconjunto
-- de `α`. Si `S : set α` es un subconjunto, entonces existe un filtro
-- `𝓟 S` correspondiente a `S` que es la colección de todos los
-- subconjuntos de `α` que contienen a `S`. Sin embargo, puede haber
-- otros filtros en `α` correspondientes a cosas que son un poco más
-- generales que los subconjuntos. Por ejemplo si `α` es un espacio
-- topológico y `x : α` entonces hay un filtro `𝓝 x` correspondiente a
-- "un entorno infinitesimal de `x`" tal que no hay ningún conjunto
-- abierto más pequeño que contenga a `x`. Como otro ejemplo, si `α`
-- está ordenado entonces hay un filtro de "entornos del infinito" en
-- `α` aunque aunque no haya ningún `∞` en `α`.
--
-- Si `F` es un filtro, entonces se puede pensar en `F` como un tipo
-- generalizado de subconjunto `F` de `α`, y debes pensar que `S ∈ F`
-- significa `F ⊆ S`. Tener esto en cuenta te ayudará a motivar los
-- axiomas que vienen a continuación.

-- =====================================================================
-- § Definición de filtro                                             --
-- =====================================================================

-- Esta es la definición formal. Un filtro sobre `α` es una colección
-- `F` de subconjuntos de `α` que satisface los tres axiomas siguientes:
-- 1. `α ∈ F` (en Lean se escribe `univ ∈ F` porque se distingue
--    entre el tipo `α` y el término `univ : set α` correspondiente a `α`)
-- 2. Si `S ∈ F` y `S ⊆ T` entonces `T ∈ F`; es decir, `F` es "cerrado
--    hacia arriba".
-- 3. Si `A ∈ F` y `B ∈ F` entonces `A ∩ B ∈ F`; es decir, `F` es
--    cerrado bajo intersecciones binarias.
--
-- Obsérvese que (1) y (3) implican conjuntamente (y son de hecho equivalentes a
-- la afirmación de que `F` es cerrado bajo todas las intersecciones finitas;
-- es decir, la intersección de un número finito de elementos de `F` está en `F`.
--
-- Esta es la definición de Lean:
--    structure filter (α : Type*) :=
--    (sets                   : set (set α))
--    (univ_sets              : set.univ ∈ sets)
--    (sets_of_superset {x y} : x ∈ sets → x ⊆ y → y ∈ sets)
--    (inter_sets {x y}       : x ∈ sets → y ∈ sets → x ∩ y ∈ sets)
--
-- En palabras, `filter α` es el tipo de filtros sobre `α`, por lo que
-- dar un filtro en `α` es dar un término `F : filter α` de tipo `filter
-- α`. Para obtener un término de tipo `filter α` hay que dar una
-- colección `conjuntos` de subconjuntos de `α` y luego tres pruebas de
-- los tres axiomas.
--
-- Un ejemplo bastante simple de un filtro es el filtro de *todos* los
-- subconjuntos de `α`. Aquellos que hayan visto definiciones de
-- filtros en otros lugares (por ejemplo en Bourbaki) habrán visto un
-- axioma adicional en la definición de un filtro que dice que un filtro
-- no puede ser la colección de todos los subconjuntos de subconjuntos
-- de `α`. Esto resulta ser un axioma poco natural, es como es como
-- exigir en la teoría de los ideales que si `R` es un anillo entonces
-- `R` no puede ser un ideal de `R`. Una ventaja de esta definición de
-- ideal sería que un ideal maximal de `R` sería literalmente un
-- elemento maximal de los ideales de `R`, pero esta ventaja se ve
-- compensada por la desventaja de que la definición se vuelve mucho
-- menos functorial (por ejemplo, la imagen de un ideal a lo largo de
-- un homomorfismo de anillo podría no ser un ideal, no se puede en
-- general sumar dos ideales, etc.). Para preservar la funtorialidad de
-- los filtros, mathlib no tiene este axioma de Bourbaki como un axioma
-- para los filtros. En consecuencia, hay dos filtros "extremos" en `α`,
-- a saber, el que sólo contiene `univ` (nótese que esto es forzado por
-- `univ_sets`), y luego el que mencionamos antes, que contiene todos
-- los subconjuntos de `α`. Estos dos filtros se llaman `⊥` y `⊤`,
-- ¡aunque te sorprenderá saber cuál es cada uno!  El filtro formado por
-- todos los subconjuntos de `α` es el que corresponde al conjunto vacío,
-- por lo que es `⊥`, y el que consta sólo de `univ` es el es el
-- correspondiente al conjunto de `α`, por lo que es `⊤`.

-- =====================================================================
-- § Notación, tácticas útiles y teoremas útiles                      --
-- =====================================================================

-- No vamos a construir filtros desde los primeros principios, en su
-- lugar usaremos la API de Lean para los filtros.
--
-- Sean `α : Type`, `F : filter α` y `S : set α`. La notación
-- `S ∈ F` se se define como `S ∈ F.sets`.
--
-- La táctica `ext` puede utilizarse para reducir un objetivo `F = G` a
-- un objetivo de la forma `∀ S, S ∈ F ↔ S ∈ G`.
--
-- Los campos de la estructura mencionan cosas como `S ∈ F.sets`, por lo
-- que los axiomas se repiten con otros nombres, pero utilizando la
-- notación `S ∈ F`. Los lemas correspondientes a las definiciones son:
--    `univ_mem_sets : univ ∈ F`
--    `mem_sets_of_superset : S ∈ F → S ⊆ T → T ∈ F`
--    `inter_mem_sets : S ∈ F → T ∈ F → S ∩ T ∈ F`
--
-- Estos lemas están en el espacio de nombres `filter`; es decir, sus
-- nombres completos son `filter.univ_mem_sets`, etc. Pero usaremos
-- "open filter", lo que significa que no se necesita escribir el
-- prefijo `filter.` delante de cada lema que necesites sobre
-- filtros. De hecho, también usaremos un montón de cosas sobre
-- conjuntos, como `set.inter_subset_left`, así que también usaremos
-- `open set`.

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir los espacios de nombre de los filtros y de los
-- conjuntos.
-- ---------------------------------------------------------------------

open filter set

-- ---------------------------------------------------------------------
-- Ejercicio. Declara las variables
-- + α sobre tipos
-- + F sobre filtros sobre α
-- + S y T sobre conjunros de elementos de tipo α.
-- ---------------------------------------------------------------------

variable  (α : Type)
variable  (F : filter α)
variables (S T : set α)

-- He aquí un lema sobre los filtros: Dos conjuntos `S` y `T` están
-- ambos en un filtro `F` si su intersección lo está. Para demostrarlo,
-- es útil conocer los siguientes resultados (del espacio de nombres de
-- los conjuntos)
-- + `inter_subset_left S T : S ∩ T ⊆ S`
-- + `inter_subset_right S T : S ∩ T ⊆ S`

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    S ∩ T ∈ F ↔ S ∈ F ∧ T ∈ F
-- ---------------------------------------------------------------------

-- Demostración (por doble implicación):
-- (⟹) Supongamos que S ∩ T ∈ F. Entonces, S ∩ T ⊆ S y, por el axioma
-- mem_sets_of_superset, se tiene que S ∈ F. Análogamente se demuestra
-- que T ∈ F.
--
-- (⟸) S ∈ F ∧ T ∈ F. Entonces, S ∩ T ∈ F por el axioma inter_mem_sets.

example : S ∩ T ∈ F ↔ S ∈ F ∧ T ∈ F :=
begin
  split,
  { intro hST,
    split,
    { apply mem_sets_of_superset hST,
      exact inter_subset_left S T },
    { apply mem_sets_of_superset hST,
      exact inter_subset_right S T } },
  { rintros ⟨hS, hT⟩,
    exact inter_mem_sets hS hT }
end

-- El filtro principal `𝓟 X` generado por `X : set α` es el conjunto de
-- los subconjuntos de `α` que contienen a `X`. Se demostrará que es un
-- filtro. Para ello, son útiles los siguientes lemas:
--    `mem_univ s : s ∈ univ`
--    `subset.trans : A ⊆ B → B ⊆ C → A ⊆ C`
--    `subset_inter : X ⊆ S → X ⊆ T → X ⊆ S ∩ T`
-- (nótese que probablemente podrías demostrar estas dos últimas cosas
-- directamente, pero también podemos usar la interfaz para conjuntos
-- dado que existe)
--    `mem_set_of_eq : x ∈ {a : α | p a} = p x`
-- (este es por definición, así que podrías usar `change` en su lugar, o
-- simplemente no reescribirlo en absoluto)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el filtro principal `𝓟 X` generado por `X`
-- es un filtro.
-- ---------------------------------------------------------------------

-- Demostración: Se define una estructura (que en mathlib se llama
-- `𝓟 X`) formada por los subconjuntos de α que contienen a X y se
-- prueba que cumple los axiomas de filtro. Concretamente, la definición
-- es
--    𝓟 X = {S : set α | X ⊆ S}
-- y las demostraciones de los axiomas son:
--
-- (1º axioma) univ ∈ 𝓟 X ya que X ⊆ univ.
--
-- (2º axioma): Sean S ∈ 𝓟 X y S ⊆ T. Entonces, X ⊆ S y, por la
-- transitiva, X ⊆ T. Por tanto, T ∈ 𝓟 X.
--
-- (3º axioma): Sean S, T ∈ 𝓟 X. Entonces, X ⊆ S y X ⊆ T. Por tanto,
-- X ⊆ S ∩ T. Luego, S ∩ T ∈ 𝓟 X.

example (X : set α) : filter α :=
{ sets := {S : set α | X ⊆ S},
  univ_sets :=
  begin
    intros S hS,
    exact mem_univ _,
  end,
  sets_of_superset :=
  begin
    intros S T hS hT,
    change X ⊆ T,
    change X ⊆ S at hS,
    exact subset.trans hS hT,
  end,
  inter_sets :=
  begin
    intros S T hS hT,
    rw mem_set_of_eq at *,
    exact subset_inter hS hT,
  end }

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir localmente el entorno filter para poder usar la
-- notación `𝓟 X` para el filtro principal generado por `X`.
-- ---------------------------------------------------------------------

open_locale filter

-- =====================================================================
-- § El orden (≤) sobre filtros                                       --
-- =====================================================================

-- Lo siguiente no es sorprendente: la colección de todos los filtros
-- sobre `α` está parcialmente ordenada. Tal vez sea más sorprendente:
-- el orden es al revés de lo que se esperaría. Si `F` y `G` son filtros
-- en `α`, entonces `F ≤ G` se define como `G.sets ⊆ F.sets`; es decir,
-- cada conjunto en el filtro `G` está también en el filtro `F`. ¿A qué
-- se debe esto? Pues bien, piensa en los filtros principales. Si `S ⊆
-- T` son dos subconjuntos, entonces `X ∈ 𝓟 T` implica `T ⊆ X`, luego `S
-- ⊆ X` y `X ∈ 𝓟 S`. Cuanto más pequeño sea el conjunto, mayor será la
-- colección de conjuntos en su filtro principal.
--
-- Formalicemos esto. Demostremos que 𝓟 S ≤ 𝓟 T ↔ S ⊆ T.
-- Nótese que esto es el lema `principal_mono` en mathlib pero
-- no hay inconveniente en demostrarlo por uno mismo.
--
-- Algunos lemas útiles para su demostración son:
-- + `le_def : F ≤ G ↔ ∀ (S : set α), S ∈ G → S ∈ F`
-- + `mem_principal_sets : T ∈ 𝓟 S ↔ S ⊆ T`
-- + `mem_principal_self S : S ∈ 𝓟 S`

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    𝓟 S ≤ 𝓟 T ↔ S ⊆ T
-- ---------------------------------------------------------------------

-- Demostración (por doble implicación)
-- (⟹) Supongamos que 𝓟 S ≤ 𝓟 T.
--       T ⊆ T ⟹ T ∈ 𝓟 T    [por definición de 𝓟 T]
--             ⟹ T ∈ 𝓟 S    [por definición de 𝓟 S ≤ 𝓟 T]
--             ⟹ S ⊆ T      [por definición de 𝓟 S]
-- (⟸) Supongamos que S ⊆ T. Para probar que 𝓟 S ≤ 𝓟 T, sea X ∈ 𝓟 T.
-- Entonces,
--       X ∈ 𝓟 T ⟹ T ⊆ X    [por definición de 𝓟 T]
--               ⟹ S ⊆ X    [porque S ⊆ T]
--               ⟹ X ∈ 𝓟 S  [por definición de 𝓟 S]

-- 1ª demostración
example : 𝓟 S ≤ 𝓟 T ↔ S ⊆ T :=
begin
  split,
  { intro h,
    rw le_def at h,
    have hT : T ∈ 𝓟 T := mem_principal_self T,
    specialize h T hT,
    rwa mem_principal_sets at h },
  { intro hST,
    rw le_def,
    intros X hX,
    rw mem_principal_sets at *,
    exact subset.trans hST hX }
end

-- 2ª demostración
example : 𝓟 S ≤ 𝓟 T ↔ S ⊆ T :=
-- by library_search
principal_mono

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    F ≤ 𝓟 S ↔ S ∈ F
-- ---------------------------------------------------------------------

-- Demostración (por doble implicación)
-- (⟹) Supongamos que F ≤ 𝓟 S. Se tiene,
--    S ⊆ S ⟹ S ∈ 𝓟 S   [por def. de 𝓟 S]
--          ⟹ S ∈ F     [por def. de F ≤ 𝓟 S]
-- (⟸) Supongamos que S ∈ F. Para probar que F ≤ 𝓟 S, sea X ∈ 𝓟 S. Se
-- tiene,
--     X ∈ 𝓟 S ⟹ S ⊆ X   [por def. de 𝓟 S]
--             ⟹ X ∈ F   [porque F es un filtro y S ∈ F]

-- 1ª demostración
example : F ≤ 𝓟 S ↔ S ∈ F :=
begin
  split,
  { intro h,
    rw le_def at h,
    apply h,
    exact mem_principal_self S,},
  { rw le_def,
    intros hSF X hX,
    rw mem_principal_sets at hX,
    exact mem_sets_of_superset hSF hX },
end

-- 2ª demostración
example : F ≤ 𝓟 S ↔ S ∈ F :=
-- by library_search
le_principal_iff

-- =====================================================================
-- § Los filtros son retículos completos                              --
-- =====================================================================

-- Al igual que es posible hablar del espacio topológico generado por
-- una colección de subconjuntos de `α` (es la topología más pequeña
-- para la que los subconjuntos dados son todos abiertos) también es
-- posible hablar del filtro generado por una colección de subconjuntos
-- de `α`. Se puede definir como la intersección de todos los filtros
-- que contienen a la colección dada de subconjuntos.
--
-- En la teoría del orden, dado un orden parcial (como el orden parcial
-- de los filtros) se puede empezar a preguntar si existen ínfimos y
-- supremos. Los filtros son un ejemplo donde todas estas cosas existen
-- (ínfimos y supremos finitos e infinitos) y satisfacen una colección
-- natural de axiomas, convirtiéndolos en lo que se llama un *retículo
-- completo*. Se puede demostrar esto mostrando que "filtro generado por
-- estos conjuntos" y "conjuntos subyacentes de un filtro" son funtores
-- adjuntos y luego utilizando la teoría de las inserciones de
-- Galois. Ya hablé un poco de esto al estudiar los subgrupos, y no
-- hablaré de ello de nuevo.

-- =====================================================================
-- § Otros ejemplos de filtros                                        --
-- =====================================================================

-- =====================================================================
-- §§ Filtro de los grandes en conjuntos totalmente ordenados         --
-- =====================================================================

-- Sea `L` un conjunto totalmente ordenado no vacío. Digamos que un
-- subconjunto `X` de `L` es "grande" si existe `x : L` tal que para
-- todo `y ≥ x`, `y ∈ X`. En mathlib, se denota pot `at_top L`.
--
-- Probaremos que los subconjuntos grandes son un filtro. La idea
-- matemática es que los "grandes subconjuntos" son las entornos de `∞`,
-- por lo que el correspondiente filtro es alguna representación de un
-- entorno infinitesimal de `∞`.
--
-- Notas de implementación: `linear_order L` es el tipo de órdenes
-- lineales sobre `L`.  Además, `e : L` es una forma sencilla de decir
-- que `L` no es vacío.
--
-- Recordemos que `max x y` es el máximo de x e y en un `orden lineal`, y
-- `le_max_left a b : a ≤ max a b` y análogamente `le_max_right`.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si L es un orden lineal no vacío, el
-- conjunto de sus conjuntos grandes es un filtro sobre L.
-- ---------------------------------------------------------------------

-- Demostración. El conjunto de los conjuntos grandes de L es
--    F = {X : set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X}
-- Tenemos que demostrar que F es un filtro probando los tres axiomas de
-- filtro.
--
-- (1ª axioma) Para demostrar que univ ∈ F, sea e cualquier elemento de
-- L (existe por ser L no vacío). Por la definición de univ, se tiene
--    ∀ y, e ≤ y → y ∈ univ
-- Por tanto, univ ∈ F.
--
-- (2º axioma) Sea X ∈ F e X ⊆ Y. De X ∈ F se deduce que existe un x ∈ L
-- tal que
--    ∀ y, x ≤ y → y ∈ X
-- y, puesto que X ⊆ Y, se tiene que
--    ∀ y, x ≤ y → y ∈ X
-- Por tanto, Y ∈ F.
--
-- (3º axioma) Sean X, Y ∈ F. Por la definición de F, existen x, y ∈ L
-- tales que
--    ∀ z, x ≤ z → z ∈ X
--    ∀ z, y ≤ z → z ∈ Y
-- Luego,
--    ∀ z, máx(x,y) ≤ z → z ∈ X ∩ Y
-- Por tanto, X ∩ Y ∈ F.

def at_top
  (L : Type)
  [linear_order L]
  (e : L)
  : filter L :=
{ sets := {X : set L | ∃ x : L, ∀ y, x ≤ y → y ∈ X},
  univ_sets :=
  begin
    use e,
    intros y hy,
    exact mem_univ y,
  end,
  sets_of_superset :=
  begin
    rintros X Y ⟨x, hX⟩ hXY,
    rw mem_set_of_eq,
    use x,
    intros y hxy,
    rw subset_def at hXY,
    apply hXY,
    exact hX _ hxy,
  end,
  inter_sets :=
  begin
    rintros X Y ⟨x, hX⟩ ⟨y, hY⟩,
    use max x y,
    intros z hz,
    split,
    { apply hX,
      apply le_trans _ hz,
      exact le_max_left x y },
    { apply hY,
      apply le_trans _ hz,
      exact le_max_right x y, },
  end }

-- =====================================================================
-- §§ El filtro cofinito                                              --
-- =====================================================================

-- El *filtro cofinito* sobre un tipo `α` tiene como conjuntos los
-- subconjuntos `S : set α` con la propiedad de que `Sᶜ`, el complemento
-- de `S`, es finito. Demostremos que es un filtro.
--
-- Lemas que pueden ser útiles en su demostración:
--    `compl_univ : univᶜ = ∅`
--    `finite_empty : finite ∅`
--    `compl_subset_compl : Xᶜ ⊆ Yᶜ ↔ Y ⊆ X`
--    `finite.subset : S.finite → ∀ {T : set α}, T ⊆ S → T.finite`
--    `compl_inter S T : (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ`
--    `finite.union : S.finite → T.finite → (S ∪ T).finite`
--
-- Nota. Si estás pensando "Nunca podría usar Lean por mí mismo, no
-- conozco los nombres de todos los lemas, así que tengo que confiar en
-- que el enunciado me los diga". Se pueden encontrar los lemas
-- presionando Mayúscula-espacio y las reglas para formar sus nombres.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el conjunto de los subconjuntos de α cuyo
-- complementario es finito es un filtro sobre α.
-- ---------------------------------------------------------------------

-- Demostración. Sea
--    F = {S : set α | Sᶜ es finito}
-- Tenemos que demostrar que F es un filtro probando los tres axiomas de
-- filtro.
--
-- (1ª axioma). Puesto que univᶜ = ∅, que es finito, se tiene que
-- univ ∈ F.
--
-- (2º axioma). Sean S ∈ F y S ⊆ T. Entonces, Sᶜ es finito y
-- Tᶜ ⊆ Sᶜ. Por tanto, Tᶜ es finito y T ∈ F.
--
-- (3ª axioma). Sean S, T ∈ F. Entonces, Sᶜ y Tᶜ son finitos y, puesto
-- que
--    (S ∩ T)ᶜ = Sᶜ ∪ Tᶜ
-- también (S ∩ T)ᶜ es finito. Por tanto, S ∩ T ∈ F.

def cofinite (α : Type) : filter α :=
{ sets := {S : set α | (Sᶜ).finite},
  univ_sets :=
  begin
    rw mem_set_of_eq,
    rw compl_univ,
    exact finite_empty,
  end,
  sets_of_superset :=
  begin
    intros S T hS hST,
    rw mem_set_of_eq at *,
    rw ← compl_subset_compl at hST,
    exact finite.subset hS hST,
  end,
  inter_sets :=
  begin
    intros S T hS hT,
    rw mem_set_of_eq at *,
    rw compl_inter,
    exact finite.union hS hT,
  end }

-- =====================================================================
-- § Ejercicios                                                       --
-- =====================================================================

-- No es necesario que sepas hacer los siguientes ejercicios para pasar
-- a la parte de topología del tema. Los ejercicios son
-- 1. Demostrar que el filtro cofinito en un tipo finito es el filtro
--    del conjunto de potencias entero.
-- 2. Demostrar que el filtro cofinito sobre `ℕ` es igual al filtro
--    de los subconjuntos grandes (i.e., `at_top`).
-- 3. Demostrar que el filtro cofinito sobre `ℤ` no es igual al filtro
--    de los subconjuntos grandes (i.e., `at_top`).
-- 4. Demostrar que el filtro cofinito sobre `ℕ` no es principal.
--
-- Puedes probarlos en Lean pero tendrás que dominar los conceptos de la
-- finitud. Aquí, por ejemplo, están algunas de las ideas que
-- necesitarás para hacer (4) en Lean. La prueba utiliza varios lemas de
-- la API de conjuntos, como los siguientes:
-- + filter.ext_iff {α : Type u} {f g : filter α} :
--      f = g ↔ ∀ (s : set α), s ∈ f ↔ s ∈ g
-- + diff_eq_compl_inter {α : Type u} {s t : set α} :
--      s \ t = tᶜ ∩ s
-- + compl_inter {α : Type u} (s t : set α) :
--      (s ∩ t)ᶜ = sᶜ ∪ tᶜ
-- + compl_compl {α : Type u} [boolean_algebra α] (x : α) :
--      xᶜᶜ = x
-- + set.finite_singleton {α : Type u} (a : α) :
--      {a}.finite
-- + mem_diff_singleton {α : Type u} {x y : α} {s : set α} :
--      x ∈ s \ {y} ↔ x ∈ s ∧ x ≠ y
--
-- También se necesitan los dos lemas siguientes que no están en mathlib:

lemma infinite_of_finite_compl
  {α : Type}
  [infinite α]
  {s : set α}
  (hs : sᶜ.finite)
  : s.infinite :=
λ h, set.infinite_univ (by simpa using hs.union h)

lemma set.infinite.nonempty
  {α}
  {s : set α}
  (h : s.infinite)
  : ∃ a : α, a ∈ s :=
let a := set.infinite.nat_embedding s h 37 in ⟨a.1, a.2⟩

lemma mem_cofinite
  {S : set ℕ}
  : S ∈ cofinite ℕ ↔ Sᶜ.finite :=
begin
  refl
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el filtro cofinito sobre `ℕ` no es
-- principal.
-- ---------------------------------------------------------------------

-- Demostración. Basta demostrar que para cualquier S ⊆ ℕ, el filtro
-- principal de S no es el filtro cofinito. Lo haremos por reducción al
-- absurdo. Para ello, supongamos que existe un S ⊆ ℕ cuyo filtro
-- principal es el filtro cofinito; es decir,
--    {X : set ℕ | S ⊆ X} = {X : set ℕ | Xᶜ es finito}               (1)
-- Luego, Sᶜ es finito (ya que S ⊆ S) y, por tanto, S es infinito lo que
-- significa que existe un a ∈ S. Sea T = S \ {a}. Entonces,
--    Tᶜ = (S \ {a})ᶜ = Sᶜ ∪ {a}
-- lo que implica que Tᶜ es finito y, por (1), S ⊆ T; es decir,
-- S ⊆ S \ {a} con a ∈ S lo que es una contradicción.

theorem cofinite_not_principal :
  ∀ S : set ℕ, cofinite ℕ ≠ 𝓟 S :=
begin
  intros S h,
  rw filter.ext_iff at h,
  have hS := h S,
  rw mem_cofinite at hS,
  have hS2 : Sᶜ.finite,
  { rw hS,
    apply mem_principal_self },
  { clear hS,
    have hS3 := infinite_of_finite_compl hS2,
    have hS4 : ∃ s : ℕ, s ∈ S := set.infinite.nonempty hS3,
    cases hS4 with a ha,
    set T := S \ {a} with hTdef,
    specialize h T,
    have hT : T ∈ cofinite ℕ,
    { rw [mem_cofinite, hTdef, diff_eq_compl_inter, compl_inter, compl_compl],
      apply finite.union _ hS2,
      apply finite_singleton },
    rw h at hT,
    rw mem_principal_sets at hT,
    specialize hT ha,
    rw [hTdef, mem_diff_singleton] at hT,
    cases hT with _ hcontra,
    apply hcontra,
    refl, },
end
