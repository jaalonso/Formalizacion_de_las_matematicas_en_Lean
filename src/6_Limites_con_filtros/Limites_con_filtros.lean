-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de filtros sobre conjuntos.
-- ---------------------------------------------------------------------

import order.filter.basic

-- =====================================================================
-- § La función tendencia (`tendsto`)                                  --
-- =====================================================================

-- Si `X` y `Y` son tipos, `φ : X → Y` es una función, `F : filter X` y
-- `G : filter Y` son filtros, entonces `filter.tendsto φ F G` es una
-- afirmación verdadero-falso, que se pronuncia algo así como "`F`
-- tiende a `G` a lo largo de `φ`". Por supuesto, vamos a usar `open
-- filter` en este archivo, por lo que puede escribir simplemente
-- `tendsto φ F G`, o si te gusta la notación de puntos puedes incluso
-- escribir `F.tendsto φ G`.

-- =====================================================================
-- § Significado geométrico de tendencia (`tendsto`)                  --
-- =====================================================================

-- Empecemos pensando el caso fácil en el que `F` y `G` son en realidad
-- subconjuntos de `X` y `Y` (es decir, filtros principales, asociados a
-- conjuntos que también llamaremos `F` y `G`). En este caso
-- `tendsto φ F G` significa simplemente que "`φ` se restringe a una
-- función de `F` a `G`", o en otras palabras `∀ x ∈ F, φ(x) ∈ G`.
--
-- Hay otras dos formas de escribir este predicado. La primera implica
-- empujar un conjunto hacia adelante mediate una aplicación. Si `F` es
-- un subconjunto de `X` entonces `φ(F)` denota la imagen de `F` bajo
-- `φ`, es decir es decir, el subconjunto `{y : Y | ∃ x : X, φ x = y}`
-- de `Y`. Entonces, `tendsto φ F G` significa simplemente `φ(F) ⊆ G`.
--
-- La segunda implica retroceder un conjunto mediante una aplicación. Si
-- `G` es un subconjunto de `Y` entonces `φ-¹(G)` denota la preimagen de
-- `G` bajo `φ`; es decir, el subconjunto `{x : X | φ x ∈ G}` de
-- `Y`. Entonces `tendsto φ F G` significa simplemente `F ⊆ φ-¹(G)`.
--
-- Así es como funciona todo en el caso de los conjuntos. Lo que tenemos
-- que hacer hacer hoy es averiguar cómo empujar hacia adelante y tirar
-- hacia atrás filtros mediante una aplicación `φ`. Una vez hecho esto,
-- podemos demostrar que `φ(F) ≤ G ↔ F ≤ φ-¹(G)` y utilizar cualquiera
-- de estos como nuestra definición de `tendsto φ F G`, no importa cuál.

-- =====================================================================
-- § Digresión: funtores adjuntos                                     --
-- =====================================================================

-- La siguiente discusión no es necesaria para poder hacer los problemas
-- de esta semana, pero puede proporcionar algunos antecedentes útiles.
-- También hay que tener en cuenta que cualquiera que no le guste la
-- palabra "tipo" puede literalmente cambiarla por la palabra "conjunto"
-- (y cambiar "término de tipo" por "elemento del conjunto"), que es
-- como los argumentos de esta clase aparecen en la literatura
-- matemática tradicional.
--
-- Los tipos parcialmente ordenados, como el tipo de subconjuntos de un
-- tipo fijo tipo `X` o el tipo de los filtros en `X`, son en realidad
-- ejemplos de categorías. En general, si "P" es un tipo parcialmente
-- ordenado y `x, y` son términos del tipo `P`, la idea es que podemos
-- definir que `Hom(x,y)` tiene un elemento si `x ≤ y` es verdadero y
-- ningún elemento si "x ≤ y" es falso. Los axiomas de una categoría son
-- que `Hom(x,x)` tiene un elemento identidad, lo que se deduce de la
-- reflexividad de `≤`, y que se pueden componer morfismos, lo que se
-- deduce de la transitividad de `≤`. La antisimetría establece que si
-- dos objetos son isomorfos (es decir, en este caso, si `Hom(x,y)` y
-- `Hom(y,x)` son ambos no vacíos), entonces son iguales. Si `φ : X → Y`
-- es una aplicación de tipos, entonces las imágenes y contraimágenes
-- son ambos funtores del `set X` al `set Y`, porque `S ⊆ T → φ(S) ⊆
-- φ(T)` y `U ⊆ V → φ-¹(U) ⊆ φ-¹(V)`. La afirmación de que `φ(S) ≤ U ↔ S
-- ≤ φ-¹(U)` es simplemente la afirmación de que estos funtores son
-- adjuntos entre sí. Hoy definiremos progrediente y regrediente para
-- filtros, y mostraremos que también son un par de funtores adjuntos,
-- pero no utilizaremos este lenguaje. De hecho, existe un lenguaje
-- especial para los funtores adjuntos en esta sencilla situación:
-- diremos que pushforward y pullback forman una conexión de Galois.

-- =====================================================================
-- § Aplicaciones progredientes y regredientes                        --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Declara las variables
-- + X, Y sobre tipos
-- + f sobre funciones de X en Y.
-- ---------------------------------------------------------------------

variables (X Y : Type)
variable  (f : X → Y)

-- =====================================================================
-- §§ Imágenes directas de conjuntos                                  --
-- =====================================================================

-- En Lean, la imagen `f(S)` de un subconjunto `S : set X` no puede
-- denotarse por `f S`, porque `f` espera un elemento de `X` como
-- argumento, no un subconjunto de `X`, por lo que necesitamos
-- una nueva notación.
--
-- Notación : `f '' S` es la imagen de `S` bajo `f`. Vamos a
-- comprobarlo.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f '' S = {y : Y | ∃ x : X, x ∈ S ∧ f x = y}
-- ---------------------------------------------------------------------

example
  (S : set X)
  : f '' S = {y : Y | ∃ x : X, x ∈ S ∧ f x = y} :=
begin
  refl
end

-- =====================================================================
-- § Imágenes inversas de conjuntos                                   --
-- =====================================================================

-- En Lean, la imagen invers `f-¹(T)` de un subconjunto `T : set Y` no
-- puede denotarse como `f-¹ T` porque `-¹` es la notación para la
-- inversa de f que es una función de `Y` a `X`, no una función sobre
-- subconjuntos de `Y`.
--
-- Notación : `f -¹' T` es la imagen inversa de `T` bajo `f`.
--
-- Se escribe `\-1'` para `-¹'`

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    f ⁻¹' T = {x : X | f x ∈ T}
-- ---------------------------------------------------------------------

example
  (T : set Y)
  : f ⁻¹' T = {x : X | f x ∈ T} :=
begin
  refl
end

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre de conjuntos.
-- ---------------------------------------------------------------------

open set

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que las siguientes condiciones son
-- equivalentes:
-- 1) `f '' S ⊆ T`
-- 2) `S ⊆ f-¹' T`
--
-- Para demostrarlo, es útil el lema
--    mem_preimage : a ∈ f -¹' s ↔ f a ∈ s`
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (S : set X)
  (T : set Y)
  : f '' S ⊆ T ↔ S ⊆ f⁻¹' T :=
begin
  split,
  { intros h x hxS,
    rw subset_def at h,
    rw mem_preimage,
    apply h,
    rw mem_image,
    use [x, hxS, rfl] },
  { intros h y hxy,
    rw mem_image at hxy,
    rcases hxy with ⟨x, xS, fxy⟩,
    rw ← fxy,
    specialize h xS,
    rw mem_preimage at h,
    exact h, }
end

-- 2ª demostración
example
  (S : set X)
  (T : set Y)
  : f '' S ⊆ T ↔ S ⊆ f⁻¹' T :=
begin
  split,
  { intros h x hxS,
    apply h,
    use [x, hxS, rfl] },
  { rintros h - ⟨x, hxS, rfl⟩,
    exact h hxS }
end

-- 3ª demostración
example
  (S : set X)
  (T : set Y)
  : f '' S ⊆ T ↔ S ⊆ f⁻¹' T :=
-- by library_search
image_subset_iff

-- =====================================================================
-- § Filtros progredientes                                            --
-- =====================================================================

-- La imagen directa es fácil, así que vamos a hacer eso primero.  Se
-- llama `filter.map` en Lean.
--
-- Definimos el filtro progrediente `map f F` en `Y` como sigue:
-- un subconjunto de `Y` está en `map f F` si `f-¹(Y)`
-- está en `F`.
--
-- Vamos a probar que `map f F` es un filtro. Para ello, serán útiles
-- los siguientes lemas:
-- + mem_set_of_eq {α : Type u} {a : α} {p : α → Prop} :
--      a ∈ {x : α | p x} = p a
-- + univ_mem_sets {α : Type u} {f : filter α} :
--      univ ∈ f
-- + mem_sets_of_superset {α : Type u} {f : filter α} {x y : set α} :
--      x ∈ f → x ⊆ y → y ∈ f
-- + inter_mem_sets {α : Type u} {f : filter α} {s t : set α} :
--      s ∈ f → t ∈ f → s ∩ t ∈ f

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre de los filtros.
-- ---------------------------------------------------------------------

open filter

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que `map f F` es un filtro.
-- ---------------------------------------------------------------------

-- Demostración. Por definición, `map f F` es
--    G = {T : set Y | f ⁻¹' T ∈ F}
-- Tenemos que demostrar que G es un filtro comprobando que cumple los
-- axiomas.
--
-- (1º axioma: univ_sets). Tenemos que
--    f ⁻¹' univ
--    = univ       [por preimage_univ]
--    ∈ F          [porque F es un filtro]
-- Por tanto, univ ∈ G.
--
-- (2º axioma: sets_of_superset). Sean S y T tales que S ∈ G y S ⊆ T. Se
-- tiene, f ⁻¹' S ∈ F (porque S ∈ G). Veamos que f ⁻¹' S ⊆ f ⁻¹' T. Para
-- ello, sea x ∈ f ⁻¹' S.  Entonces,
--     x ∈ f ⁻¹' S
--     ⟹ f x ∈ S        [por def. de f ⁻¹']
--     ⟹ f x ∈ T        [porque S ⊆ T]
--     ⟹ x ∈ f ⁻¹' T    [por def. de f ⁻¹']
-- Por tanto, f ⁻¹' S ⊆ f ⁻¹' T y, como f ⁻¹' S ∈ F, se tiene que
-- f ⁻¹' T ∈ F (porque F es un filtro). Luego. T ∈ G.
--
-- (3º axioma: inter_sets). Sean S, T in G. Entonces,
--    f ⁻¹' S ∈ F ∧ f ⁻¹' T ∈ F   [por def. de G]
--    ⟹ f ⁻¹' S ∩ f ⁻¹' T ∈ F   [porque F es un filtro]
--    ⟹ f ⁻¹' (S ∩ T) ∈ F       [por preimage_inter]
--    ⟹ S ∩ T ∈ G               [por def. de G]

example (F : filter X) : filter Y :=
{ sets := {T : set Y | f ⁻¹' T ∈ F},
  univ_sets :=
  begin
    rw mem_set_of_eq,
    exact univ_mem_sets,
  end,
  sets_of_superset :=
  begin
    intros S T hS hST,
    rw mem_set_of_eq at *,
    refine mem_sets_of_superset hS _,
    intros x hx,
    rw mem_preimage at *,
    exact hST hx,
  end,
  inter_sets :=
  begin
    intros S T hS hT,
    rw mem_set_of_eq at *,
    rw preimage_inter,
    exact inter_mem_sets hS hT,
  end, }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    T ∈ map f F ↔ f ⁻¹' T ∈ F
-- También se puede escribir como
--    T ∈ F.map f ↔ f ⁻¹' T ∈ F
-- ---------------------------------------------------------------------

example
  (F : filter X)
  (T : set Y)
  : T ∈ map f F ↔ f ⁻¹' T ∈ F :=
begin
  refl
end

-- Vamos a demostrar que map cumple las propiedades de los functores.
--
-- Para comprobar que dos filtros son iguales, se puede utilizar la
-- táctica `ext`.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    map id F = F
-- ---------------------------------------------------------------------

-- Demostración. Sea S ∈ X. Tenemos que demostrar que
--    S ∈ map id F ↔ S ∈ F
-- Su prueba es
--    S ∈ map id F
--    ↔ {x : X | id x ∈ S} ∈ F     [por def. de map]
--    ↔ {x : X | x ∈ S} ∈ F        [por def. de id]
--    ↔ S ∈ F                      [por def. de id]

-- 1ª demostración
example
  (F : filter X)
  : map id F = F :=
begin
  ext S,
  rw filter.mem_map,
  calc S ∈ map id F
       ↔ {x : X | id x ∈ S} ∈ F : by rw filter.mem_map
  ...  ↔ {x : X | x ∈ S} ∈ F    : by unfold id
  ...  ↔ S ∈ F                  : by refl,
end

-- 2ª demostración
example
  (F : filter X)
  : map id F = F :=
begin
  ext S,
  rw filter.mem_map,
  unfold id,
  change S ∈ F ↔ S ∈ F,
  exact iff.rfl,
end

-- 3ª demostración
example
  (F : filter X)
  : F.map id = F :=
begin
  ext S,
  refl,
end

-- 4ª demostración
example
  (F : filter X)
  : F.map id = F :=
-- by library_search
map_id

-- 5ª demostración
example
  (F : filter X)
  : map id F = F :=
begin
  apply filter_eq,
  refl,
end

-- 6ª demostración
example
  (F : filter X)
  : map id F = F :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar las siguientes variables:
-- + Z sobre tipos.
-- + g sobre funciones de Y en Z.
-- ---------------------------------------------------------------------

variable (Z : Type)
variable (g : Y → Z)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    map (g ∘ f) F = map g (map f F)
-- ---------------------------------------------------------------------

-- Demostración. Tenemos que probar que, para todo S : set Z,
--    S ∈ map (g ∘ f) F ↔ S ∈ map g (map f F)
-- Lo haremos por doble implicación.
--
-- (⟹) Supongamos que S ∈ map (g ∘ f) F. Entonces, existe un T ∈ F tal
-- que (g ∘ f)[T] ⊆ S. Luego f[T] ∈ map f F y g[f[T] ] ⊆ S. Por tanto,
-- S ∈ map g (map f F).
--
-- (⟸) Supongamos que S ∈ map g (map f F). Entonces, existe un T ∈ map f F
-- tal que g[T] ⊆ S. Luego, existe un U ∈ F tal que f[U] ⊆ T. Por tanto,
--    (g ∘ f)[U]
--    = g[f[U]]
--    ⊆ g[T]       [porque f[U] ⊆ T]
--    ⊆ S
-- Por tanto, S ∈ map (g ∘ f) F.

-- 1ª demostración
example
  (F : filter X)
  : map (g ∘ f) F = map g (map f F) :=
begin
  ext S,
  split,
  { intro h,
    rw mem_map_sets_iff at *,
    rcases h with ⟨T, hTF, gfT⟩,
    use f '' T,
    split,
    { rw mem_map_sets_iff,
      use T,
      exact ⟨hTF, rfl.subset⟩, },
    { rw ← image_comp,
      exact gfT, }},
  { intro h,
    rw mem_map_sets_iff at *,
    rcases h with ⟨T, hTF, gfT⟩,
    rw mem_map_sets_iff at hTF,
    rcases hTF with ⟨U, hUF, fU⟩,
    use U,
    split,
    { exact hUF, },
    { rw image_comp,
      calc  g '' (f '' U)
          ⊆ g '' T        : image_subset g fU
      ... ⊆ S             : gfT } },
end

-- 2ª demostración
example
  (F : filter X) :
  map (g ∘ f) F = map g (map f F) :=
begin
  ext S,
  refl,
end

-- 3ª demostración
example
  (F : filter X) :
  map (g ∘ f) F = map g (map f F) :=
-- by library_search
map_map.symm

-- 4ª demostración
example
  (F : filter X) :
  map (g ∘ f) F = map g (map f F) :=
by simp

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir localmente el entorno de filtros (para usar 𝓟).
-- ---------------------------------------------------------------------

open_locale filter

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    map f (𝓟 S) = 𝓟 (f '' S)
-- ---------------------------------------------------------------------

-- Demostración. Tenemos que demostrar que para todo T ⊆ Y,
--    T ∈ map f (𝓟 S) ↔ T ∈ 𝓟 (f '' S)
-- que es equivalente a
--    {x : X | f x ∈ T} ∈ 𝓟 S ↔ T ∈ 𝓟 (f '' S)
-- que es equivalente a
--    S ⊆ {x : X | f x ∈ T} ↔ f '' S ⊆ T
-- Lo demostraremos por doble inmplicación.
--
-- (⟹) Supongamos que
--    S ⊆ {x : X | f x ∈ T},                                         (1)
-- y sea x ∈ S. Tenemos que probar que f x ∈ T, que se tiene por (1).
--
-- (⟸) Supongamos que
--    f '' S ⊆ T                                                     (2)
-- y sea x ∈ S. Tenemos que demostrar que x ∈ {x : X | f x ∈ T}, que se
-- tiene por (2).

-- 1ª demostración
example
  (S : set X)
  : map f (𝓟 S) = 𝓟 (f '' S) :=
begin
  ext T,
  rw mem_map,
  rw mem_principal_sets,
  rw mem_principal_sets,
  split,
  { rintro h y ⟨x, hx, rfl⟩,
    exact h hx },
  { rintro h x hx,
    apply h,
    exact ⟨x, hx, rfl⟩ }
end

-- 2ª demostración
example
  (S : set X)
  : map f (𝓟 S) = 𝓟 (f '' S) :=
-- by library_search
map_principal

-- =====================================================================
-- § Tendencia ("tendsto")                                            --
-- =====================================================================

-- La definición: si `f : X → Y` y `F : filter X` y `G : filter Y`
-- entonces `tendsto f F G : Prop := map f F ≤ G`. Esto es una
-- definición (tiene tiene el tipo `Prop`), no la demostración de un
-- teorema. Es un enunciado con argumentos `f`, `F` y `G`. Es un poco
-- como decir "f es continua en x" o algo así, que puede ser verdadero o
-- puede ser falso.
--
-- Se puede leer `tendsto f F G` como `f` es una tendencia de `F` en `F`
-- (como se lee f es una función continua de F en G).

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    tendsto f F G ↔ ∀ T, T ∈ G → f ⁻¹' T ∈ F
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (F : filter X)
  (G : filter Y)
  : tendsto f F G ↔ ∀ T, T ∈ G → f ⁻¹' T ∈ F :=
begin
  refl
end

-- 2ª demostración
example
  (F : filter X)
  (G : filter Y)
  : tendsto f F G ↔ ∀ T, T ∈ G → f ⁻¹' T ∈ F :=
-- by library_search
tendsto_def

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    tendsto id F F
-- ---------------------------------------------------------------------

-- Demostración. Por la definición de tendsof, hay que demostrar que
--    ∀ T, T ∈ F → id ⁻¹' T ∈ F
-- Sea T ∈ F. Entonces, id ⁻¹' T = T ∈ F

-- 1ª demostración
example
  (F : filter X)
  : tendsto id F F :=
begin
  change ∀ T, T ∈ F → id ⁻¹' T ∈ F,
  intros T h,
  rw preimage_id,
  exact h,
end

-- 2ª demostración
example
  (F : filter X)
  : tendsto id F F :=
begin
  intro S,
  exact id,
end

-- 3ª demostración
example
  (F : filter X)
  : tendsto id F F :=
-- by library_search
tendsto_id

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si `tendsto f F G` y `tendsto g G H),
-- entonces `tendsto (g ∘ f) F H`.
-- ---------------------------------------------------------------------

--- Demostración. Por la definición de tendsto, las hipótesis son
--     ∀ (s : set Y), s ∈ G → f ⁻¹' s ∈ F                         (1)
--     ∀ (s : set Z), s ∈ H → g ⁻¹' s ∈ G                         (2)
-- y la conclusión es
--     ∀ (s : set Z), s ∈ H → g ∘ f ⁻¹' s ∈ F
-- Para demostrarla, sea S : set Z tal que S ∈ H. Por (2), g ⁻¹' S ∈ G y
-- por (1), f ⁻¹' (g ⁻¹' S) ∈ F. Por tanto, g ∘ f ⁻¹' S ∈ F.

-- 1ª demostración
example
  (F : filter X)
  (G : filter Y)
  (H : filter Z)
  (f : X → Y)
  (g : Y → Z)
  (hf : tendsto f F G)
  (hg : tendsto g G H)
  : tendsto (g ∘ f) F H :=
begin
  rw tendsto_def at *,
  rintro S hS,
  specialize hg _ hS,
  specialize hf _ hg,
  rw preimage_comp,
  exact hf,
end

-- 2ª demostración
example
  (F : filter X)
  (G : filter Y)
  (H : filter Z)
  (f : X → Y)
  (g : Y → Z)
  (hf : tendsto f F G)
  (hg : tendsto g G H)
  : tendsto (g ∘ f) F H :=
begin
  rintro S hS,
  specialize hg hS,
  specialize hf hg,
  exact hf,
end

-- 3ª demostración
example
  (F : filter X)
  (G : filter Y)
  (H : filter Z)
  (f : X → Y)
  (g : Y → Z)
  (hf : tendsto f F G)
  (hg : tendsto g G H)
  : tendsto (g ∘ f) F H :=
-- by library_search
tendsto.comp hg hf

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    tendsto (g ∘ f) F G ↔ tendsto g (map f F) G
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (g : Y → Z)
  (F : filter X)
  (G : filter Z)
  : tendsto (g ∘ f) F G ↔ tendsto g (map f F) G :=
begin
  rw tendsto_def,
  rw tendsto_def,
  split,
  { intros h S hS,
    rw mem_map,
    specialize h S hS,
    have h1 : {x : X | f x ∈ g ⁻¹' S} = g ∘ f ⁻¹' S,
    { ext y,
      split,
      { assume h1,
        rw mem_set_of_eq at h1,
        rw mem_preimage at *,
        unfold function.comp,
        exact h1, },
      { intro h1,
        rw mem_set_of_eq,
        rw mem_preimage at *,
        unfold function.comp at h1,
        exact h1, }},
    rw h1,
    exact h, },
  { intros h S hS,
    specialize h S hS,
    rw mem_map at h,
    have h1 : {x : X | f x ∈ g ⁻¹' S} = g ∘ f ⁻¹' S,
    { refl },
    { rw ← h1,
      exact h, } },
end

-- 2ª demostración
example
  (g : Y → Z)
  (F : filter X)
  (G : filter Z)
  : tendsto (g ∘ f) F G ↔ tendsto g (map f F) G :=
begin
  refl,
end

-- 3ª demostración
lemma tendsto_comp_map
  (g : Y → Z)
  (F : filter X)
  (G : filter Z)
  : tendsto (g ∘ f) F G ↔ tendsto g (map f F) G :=
-- library_search
tendsto_map'_iff.symm

-- =====================================================================
-- § Filtros regredientes                                             --
-- =====================================================================

-- No usaremos esto en la siguiente parte.
--
-- Sea `f : X → Y` y `G : filter Y`, y queremos un filtro sobre
-- `X`. Hagamos una definición ingenua. Queremos una colección de
-- subconjuntos de `X` correspondiente al filtro obtenido al retirar `G`
-- a lo largo de `f`. ¿Cuándo debe estar `S : set X` en este filtro?
-- Quizás sea cuando `f '' S ∈ G`. Sin embargo, no hay ninguna razón que
-- la colección de `S` que satisface esta propiedad sea un filtro en
-- `X`. Por ejemplo, no hay razón para esperar que `f '' univ ∈ G` si
-- `f` no es suryectiva.
--
-- Aquí hay una forma de arreglar esto. Recordemos que nuestro modelo de
-- filtro `G` es una especie de tipo de noción generalizada de
-- conjunto. Si `T : set Y` entonces `T ∈ G` se supone que significa que
-- el "conjunto" `G` es un subconjunto de `T`. Así que esto debería
-- implicar que `f-¹(G) ⊆ f-¹(T)`. En particular, si `T ∈ G` y `f-¹(T) ⊆
-- S` entonces esto debería significar que `f-¹(G) ⊆ S` y por tanto `S ∈
-- f-¹(G)`. Probemos esto y veamos si funciona.
--
-- Lemas útiles (puede que estés llegando al punto en que puedas
-- adivinar los nombres de los lemas):
-- + `subset_univ S : S ⊆ univ`
-- + `subset.trans : A ⊆ B → B ⊆ C → A ⊆ C`

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si G es un filtro de Y, entonces
--    {S : set X | ∃ T ∈ G, f ⁻¹' T ⊆ S}
-- es un filtro de X (llamado comap)
-- ---------------------------------------------------------------------

example (G : filter Y) : filter X :=
{ sets := {S : set X | ∃ T ∈ G, f ⁻¹' T ⊆ S},
  univ_sets :=
  begin
    use univ,
    split,
    { exact univ_mem_sets },
    { exact subset_univ _ }
  end,
  sets_of_superset :=
  begin
    rintros S T ⟨U, hUG, hUS⟩ hST,
    use [U, hUG],
    exact subset.trans hUS hST
  end,
  inter_sets :=
  begin
    rintro S T ⟨U, hUG, hUS⟩ ⟨V, hVG, hVT⟩,
    use [U ∩ V, inter_mem_sets hUG hVG],
    rintro x ⟨hxU, hxV⟩,
    exact ⟨hUS hxU, hVT hxV⟩,
  end }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    S ∈ comap f G ↔ ∃ T ∈ G, f ⁻¹' T ⊆ S
-- ---------------------------------------------------------------------

lemma mem_comap
  (f : X → Y)
  (G : filter Y)
  (S : set X)
  : S ∈ comap f G ↔ ∃ T ∈ G, f ⁻¹' T ⊆ S :=
begin
  refl
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    comap id G = G
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (G : filter Y)
  : comap id G = G :=
begin
  ext S,
  rw mem_comap,
  split,
  { rintro ⟨T, hT, h⟩,
    exact mem_sets_of_superset hT h,},
  { intro hS,
    use [S, hS],
    refl },
end

-- 2ª demostración
example
  (G : filter Y)
  : comap id G = G :=
-- by library_search
comap_id

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    comap (g ∘ f) H = comap f (comap g H)
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  (H : filter Z)
  : comap (g ∘ f) H = comap f (comap g H) :=
begin
  ext S,
  simp only [mem_comap],
  split,
  { rintro ⟨U, hU, h⟩,
    use g ⁻¹' U,
    refine ⟨_, h⟩,
    rw mem_comap,
    use [U, hU] },
  { rintro ⟨T, ⟨U, hU, h2⟩, h⟩,
    use [U, hU],
    refine subset.trans _ h,
    intros x hx,
    exact h2 hx }
end

lemma comap_comp
  (H : filter Z)
  : comap (g ∘ f) H = comap f (comap g H) :=
-- by library_search
comap_comap.symm

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    comap f (𝓟 T) = 𝓟 (f ⁻¹' T)
-- ---------------------------------------------------------------------

-- 1ª demostrción
example
  (T : set Y)
  : comap f (𝓟 T) = 𝓟 (f ⁻¹' T) :=
begin
  ext S,
  rw mem_comap,
  rw mem_principal_sets,
  split,
  { rintro ⟨U, hU, h⟩,
    refine subset.trans (λ x, _) h,
    apply hU },
  { intro h,
    exact ⟨T, mem_principal_self T, h⟩ }
end

-- 2ª demostración
example
  (T : set Y)
  : comap f (𝓟 T) = 𝓟 (f ⁻¹' T) :=
-- by library_search
comap_principal

-- En el siguiente ejercicio se prueba que `map f` y `comap f` son
-- funtores adjuntos o, en otras palabras, forman una conexión de
-- Galois. Es análoga a la afirmación de que si S es un subconjunto de X
-- y T es un subconjunto de Y entonces f(S) ⊆ T ↔ S ⊆ f-¹(T), siendo
-- ambas formas de decir que `f` restringe a una función de `S` a `T`.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    map f F ≤ G ↔ F ≤ comap f G
-- ---------------------------------------------------------------------


lemma filter.galois_connection
  (F : filter X)
  (G : filter Y)
  : map f F ≤ G ↔ F ≤ comap f G :=
begin
  split,
  { rintro h S ⟨T, hT, hTS⟩,
    rw le_def at h,
    exact mem_sets_of_superset (h T hT) hTS },
  { rintro h T hT,
    rw le_def at h,
    exact h (f ⁻¹' T) ⟨T, hT, subset.refl _⟩ },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que `map f` and `comap f` forman una conexión de
-- Galois.
-- ---------------------------------------------------------------------

example : galois_connection (map f) (comap f) :=
filter.galois_connection X Y f
