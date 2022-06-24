-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de las propiedades de los subconjuntos
-- de espacios topológicos.
-- ---------------------------------------------------------------------

import topology.subset_properties

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar
-- + X e Y como variables sobre espacios topológicos
-- + f como variable de funciones de X en Y.
-- ---------------------------------------------------------------------

variables (X Y : Type) [topological_space X] [topological_space Y]
variable  (f : X → Y)

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir las teorías filter y set.
-- ---------------------------------------------------------------------

open filter set

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir localmente las teorías filter (para 𝓟) y
-- topological_space (para 𝓝).
-- ---------------------------------------------------------------------

open_locale filter
open_locale topological_space

-- =====================================================================
-- § Filtros de entornos                                              --
-- =====================================================================

-- Si `α` es un espacio topológico y `a : α` entonces `𝓝 a` es el
-- siguiente filtro sobre `α`: `X ∈ 𝓝 a` si y sólo si `X` contiene un
-- entorno abierto de `a` o, equivalentemente, si `a` está en el
-- interior de `X`. Hay que pensar en `𝓝 a` como el "subconjunto
-- generalizado" de `X` correspondiente a un entorno abierto
-- infinitesimal `a`.
--
-- Utilizaremos la API de interior y clausura, y comprobaremos que `𝓝 a`
-- es un filtro.
--
-- Los siguientes lemas de los espacios topológicos serán utiles:
-- + interior_univ {α : Type u} [topological_space α] :
--      interior univ = univ
-- + mem_univ {α : Type u} (x : α) :
--      x ∈ univ
-- + interior_mono {α : Type u} [topological_space α] {s t : set α} (h : s ⊆ t) :
--     interior s ⊆ interior t
-- + interior_inter {α : Type u} [topological_space α] {s t : set α} :
--     interior (s ∩ t) = interior s ∩ interior t

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar α como una variable sobre espacios topológicos.
-- ---------------------------------------------------------------------

variables {α : Type*} [topological_space α]

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre de conjuntos.
-- ---------------------------------------------------------------------

open set

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el conjunto de los entornos abiertos de un
-- punto a (en mathlib se denota por `𝓝 a`) es un filtro.
-- ---------------------------------------------------------------------

-- Demostración. Sea a un punto. El conjunto de los entornos abiertos de
-- a es
--    F = {X : set α | a ∈ interior X}.
-- Veamos que F cumple los axiomas de filtro.
--
-- (1º axioma) univ ∈ F, ya que a ∈ univ = interior(univ).
--
-- (2º axioma): Sean X ∈ F y X ⊆ Y. Entonces,
--    a ∈ interior(X) ⊆ interior(Y)
-- Luego, a ∈ interior(Y) y Y ∈ F.
--
-- (3º axioma): Sean X, Y ∈ F. Entonces,
--    a ∈ interior(X) y a ∈ interior(Y)
--    ⟹ a ∈ interior(X) ∩ interior(Y) = interior(X ∩ Y)
-- Por tanto, X ∩ Y ∈ F.

example (a : α): filter α :=
{ sets := {X : set α | a ∈ interior X},
  univ_sets :=
  begin
    rw mem_set_of_eq,
    rw interior_univ,
    exact mem_univ a,
  end,
  sets_of_superset :=
  begin
    intros X Y haX hXY,
    rw mem_set_of_eq at *,
    exact interior_mono hXY haX,
  end,
  inter_sets :=
  begin
    intros X Y hX hY,
    rw mem_set_of_eq at *,
    rw interior_inter,
    exact ⟨hX, hY⟩
  end }

-- =====================================================================
-- § Puntos de acumulación                                            --
-- =====================================================================

-- Un punto de acumulación `a : α` de un filtro `F : filter α` en un
-- espacio topológico debe pensarse como un punto en la clausura del
-- "conjunto generalizado" correspondiente a `F`. Esta es la definición
-- formal.
--
-- Un punto de acumulación de un filtro `F : filter α` (también conocido
-- como punto límite) es `x : α` tal que `𝓝 x ⊓ F ≠ ⊥`. La imagen es que
-- la intersección del conjunto generalizado `F` y el entorno abierto
-- `𝓝 x` de `x` tienen intersección no vacía. Sin embargo, repasemos la
-- notación con más cuidado. Recordemos que el orden de los filtros es
-- al revés, por lo que `𝓝 x ⊓ F` significa el filtro generado por `F` y
-- los entornos de `x`, y `⊥` es el filtro que contiene cada
-- subconjunto. Así que esto se reduce a decir que no existen conjuntos
-- `A ∈ 𝓝 x` y `B ∈ F` tales que `A ∩ B = ∅`, o, en otras palabras, cada
-- elemento del filtro intersecta todos los entornos de `x`. Por
-- ejemplo, si `S` es un subconjunto cualquiera de `α`, entonces los
-- puntos de acumulación de `𝓟 S` son los puntos `x` tales que cualquier
-- conjunto abierto que contiene a `x` se encuentra con `S`, o lo que es
-- lo mismo, que `x` está en la cierre de `S`.
--
-- El siguiente lema (que se llama `cluster_pt.mono` en mathlib) afirma
-- que si `F` y `G` son subconjuntos generalizados de un espacio
-- topológico y `F ⊆ G`, entonces `clausura(F) ⊆ clausura(G)`.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si x es un punto de acumulación del filtro F
-- y F ≤ G, entonces x es un punto de acumulación del filtro G.
-- ---------------------------------------------------------------------

-- 1ª demostración. Sea `U ∈ 𝓝 x` y `V ∈ G`. Entonces, `V ∈ F` (porque
-- `F ≤ G`) y `U ∩ V ≠ ∅` (porque `x` es un punto de acumulación de
-- `F`). Por tanto, `x` es un punto de acumulación de `G`.

example
  {x : α}
  {F G : filter α}
  (hxF : cluster_pt x F)
  (hFG : F ≤ G)
  : cluster_pt x G :=
begin
  rw cluster_pt_iff at *,
  intros,
  apply hxF hU,
  rw filter.le_def at hFG,
  apply hFG _ hV,
end

-- 2ª demostración. Se tiene
--    𝓝 x ⊓ F ≠ ⊥          [porque x es un punto de acumulación de F]
--    𝓝 x ⊓ F ≤ 𝓝 x ⊓ G    [porque F ≤ G]
--    𝓝 x ⊓ G ≠ ⊥          [por los dos anteriores]
-- Por tanto, x es un punto de acumulación de G.

example
  {x : α}
  {F G : filter α}
  (hxF : cluster_pt x F)
  (hFG : F ≤ G)
  : cluster_pt x G :=
begin
  unfold cluster_pt,
  apply ne_bot_of_le_ne_bot hxF,
  exact inf_le_inf_left _ hFG,
end

-- 3ª demostración
example
  {x : α}
  {F G : filter α}
  (hxF : cluster_pt x F)
  (hFG : F ≤ G)
  : cluster_pt x G :=
-- by library_search
cluster_pt.mono hxF hFG

-- =====================================================================
-- § Compacidad                                                       --
-- =====================================================================

-- La definición actual de `is_compact` en mathlib dice que un
-- subconjunto `S` de un espacio topológico espacio `α` es *compacto` si
-- para cada filtro `F ≠ ⊥` tal que `S ∈ F` existe `a : α` tal que cada
-- conjunto de `F` comparte elementos con cada entorno de `a`. En otras
-- palabras, `S` es compacto si el cierre de cada subconjunto
-- generalizado no vacío `F ⊆ S` contiene algún elemento de `S`. De
-- alguna manera, la no compacidad da lugar a subconjuntos generalizados
-- que están "en el límite de `S`" pero que no intersectan un entorno de
-- elementos de "S". Tal vez sea mejor no preocuparse por esta exótica
-- definición. Por supuesto es equivalente a la definición habitual de
-- compacidad, pero no vamos a demostrarlo.
--
-- Vamos a volver a probar que un subconjunto cerrado de un espacio
-- compacto es compacto. Como antes, demostramos la afirmación más
-- general de que si `α` es cualquier espacio topológico, la
-- intersección de un subconjunto compacto de `α` y un subconjunto
-- cerrado de `α` es un subconjunto compacto de `α`.
--
-- Esta es la definición en mathlib:
--    def is_compact (s : set α) := ∀ ⦃f⦄ [ne_bot f], f ≤ 𝓟 s → ∃a∈s, cluster_pt a f
--
-- Nótese que `ne_bot f` está entre corchetes, lo que significa que el
-- sistema de inferencia de tipos lo deduce.
--
-- Una sugerencia para una prueba es primero mostrar que por la
-- compacidad de `S`, podemos encontrar un punto de acumulación `a` para
-- `f` en `s` y después demostrar que este punto de acumulación está en
-- `t` también, porque "t" es cerrado.

-- Algunos lemas útiles son:
-- + is_closed.closure_eq
--     {α : Type u} [topological_space α]
--     {s : set α}
--     (h : is_closed s)
--     : closure s = s
-- + mem_closure_iff_cluster_pt
--     {α : Type u} [topological_space α]
--     {s : set α}
--     {a : α}
--     : a ∈ closure s ↔ cluster_pt a (𝓟 s)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la intersección de un compacto s con un
-- cerrado (t) es un compacto (s ∩ t).
-- ---------------------------------------------------------------------

-- Demostración. Sea `f` un filtro tal que `f ≠ ⊥` y `f ≤ 𝓟 (s ∩ t)`.
-- Tenemos que demostrar que existe `a ∈ s ∩ t` que es un punto de
-- acumulación de `f`.
--
-- De `f ≤ 𝓟 (s ∩ t)` se sigue que `f ≤ 𝓟 s` y, por ser `s`  compacto,
-- existe `a ∈ s` que es un punto de acumulación de `f`. Pra concluir la
-- demostración, basta demostrar que `a ∈ t` (ya que entonces
-- `a ∈ s ∩ t`). Su demostración es
--    s ∩ t ⊆ s
--    ⟹ 𝓟 (s ∩ t) ≤ 𝓟 t
--           [por principal_mono]
--    ⟹ f ≤ 𝓟 t
--           [porque f ≤ 𝓟 (s ∩ t)]
--    ⟹ a es un punto de acumulación de 𝓟 t
--           [por cluster_pt.mono y serlo de f]
--    ⟹ a ∈ clausura(t)
--           [por mem_closure_iff_cluster_pt]
--    ⟹ a ∈ t
--           [por closure_eq_iff_is_closed.mpr y ser t cerrado]
--

lemma closed_of_compact
  (s : set X)
  (hs : is_compact s)
  (t : set X)
  (ht : is_closed t)
  : is_compact (s ∩ t) :=
begin
  unfold is_compact,
  intros f hnf hstf,
  haveI := hnf,
  obtain ⟨a, has, ha⟩ : ∃ a ∈ s, cluster_pt a f,
  { unfold is_compact at hs,
    apply hs,
    apply le_trans hstf,
    rw principal_mono,
    apply inter_subset_left },
  have hat : a ∈ t,
  { rw ← closure_eq_iff_is_closed.mpr ht,
    rw mem_closure_iff_cluster_pt,
    apply cluster_pt.mono ha,
    refine le_trans hstf _,
    rw principal_mono,
    apply inter_subset_right },
  exact ⟨a, ⟨has, hat⟩, ha⟩
end
