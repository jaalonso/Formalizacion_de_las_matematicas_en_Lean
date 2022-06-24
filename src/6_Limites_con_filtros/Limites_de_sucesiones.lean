-- ---------------------------------------------------------------------
-- Ejercicio. Inportar las teoría de los números reales, filtros y
-- topología.
-- ---------------------------------------------------------------------

import data.real.basic
import order.filter.at_top_bot
import topology.instances.real

-- ---------------------------------------------------------------------
-- Ejercicio. Definir localmente |x| como el valor absoluto de x.
-- ---------------------------------------------------------------------

local notation `|` x `|` := abs x

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    is_limit : (ℕ → ℝ) → ℝ → Prop
-- tal que (is_limit a l) expresa que l es el límite de la sucesión a.
-- ---------------------------------------------------------------------

definition is_limit : (ℕ → ℝ) → ℝ → Prop :=
λ a l, ∀ ε > 0, ∃ N, ∀ n ≥ N, | a n - l | < ε

-- Nota: Anteriormente vimos pruebas de propiedades de límites. A
-- continuación las volveremos a demostrar usando propiedades de filtros
-- utilizando hechos de mathlib sobre filtros.

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre de filtros.
-- ---------------------------------------------------------------------

open filter

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir localmente el espacio de nombre de espacios topógicos.
-- ---------------------------------------------------------------------

open_locale topological_space

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre de espacios métricos.
-- ---------------------------------------------------------------------

open metric

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    is_limit a l ↔ tendsto a at_top (𝓝 l)
-- ---------------------------------------------------------------------

theorem is_limit_iff_tendsto
  (a : ℕ → ℝ)
  (l : ℝ)
  : is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_at_top,
  refl,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el límite de un producto es el producto de
-- los límites.
-- ---------------------------------------------------------------------

theorem is_limit_mul
  (a b : ℕ → ℝ)
  (l m : ℝ)
  (ha : is_limit a l)
  (hb : is_limit b m)
  : is_limit (a * b) (l * m) :=
begin
  rw is_limit_iff_tendsto at *,
  exact tendsto.mul ha hb,
end

-- ¡Esta es mucho menos trabajosoa que la que vimos en la semana 3!
-- Entonces, ¿en qué dónde está el trabajo?
--
-- Las siguientes 120 líneas de este archivo discuten la primera prueba,
-- a saber `es_limit_iff_tendsto`. Está claro que los ingredientes clave
-- son `metric.tendsto_at_top`. No hay ejercicios aquí, sólo voy a
-- explicar lo que está pasando, y hablar de las definiciones (por
-- ejemplo, `es_limit`) y su coste.
--
-- La segunda prueba utiliza `is_limit_iff_tendsto` para reducir
-- `is_limit_mul` a un teorema sobre filtros, y lo demuestra con
-- `tendsto.mul`. Nosotros probaremos nuestra propia versión de
-- `tendsto.mul` en este archivo. Así que si quieres seguir con la
-- demostración puedes pasar directamente a la sección `tendsto.mul`
-- en la línea 177 más o menos.

-- =====================================================================
-- § Definiciones en Lean                                             --
-- =====================================================================

-- Cada *definición* que haces en Lean tiene un coste. Por ejemplo mira
-- la definición de Lean de `finset`, el tipo de conjuntos finitos.  Haz
-- clic con el botón derecho del ratón en `finset` y haz clic en "ir a
-- la definición". Ves una definición, y luego más de 2000 líneas de
-- teoremas sobre esta definición. No olvides cerrar el archivo después.

-- #check finset

-- Los teoremas son necesarios porque no sirve sólo definir algún
-- concepto de conjunto finito, hay que hacerlo intuitivo para el
-- usuario final, por lo que hay que demostrar que un subconjunto de un
-- conjunto finito es finito, la unión de dos conjuntos finitos es
-- finita, la imagen de un conjunto finito bajo una aplicación mapa es
-- finita, el producto de dos conjuntos finitos es finito, un producto
-- finito de conjuntos finitos indexados por un conjunto finito es
-- finito, etc. Cada uno de esos lemas de ese archivo es completamente
-- obvio para un matemático, pero necesita ser demostrado en Lean para
-- que los matemáticos puedan usar los conjuntos de la forma en que
-- intuitivamente quieren hacerlo. Mira si puedes entender algunas de
-- las afirmaciones demostradas sobre conjuntos finitos en ese
-- archivo. Ten mucho cuidado de no editarlo. Si accidentalmente lo
-- cambias, simplemente cierra el archivo archivo sin guardarlo, o usa
-- ctrl-Z para deshacer los cambios.
--
-- Cuando desarrollamos la teoría de los límites de las secuencias en la
-- semana 3, escribimos la definición `is_limit`. Esta definición tiene
-- un coste; para que sea útil para el usuario final, tenemos que
-- demostrar una tonelada de teoremas sobre `is_limit`. Esto es lo que
-- sucede en una clase de análisis de licenciatura: ves la definición y
-- luego haces lo que los informáticos llaman la "API" o la "interfaz"
-- (un montón de lemas y teoremas sobre "is_limit"); por ejemplo,
-- "is_limit_add", que dice que `aₙ → l` y `bₙ → m` implica `a_n + b_n →
-- l + m`, y también `is_limit_neg`, `es_limit_sub`, `es_limit_mul` y
-- así sucesivamente.
--

-- Pero resulta que `is_limit` es sólo un caso muy especial de
-- `tendsto`, y como `tendsto` ya está en mathlib, ya hay una gran API
-- para `tendsto` que se ha desarrollado en los últimos años. Fue
-- iniciada por el autor original de `tendsto` y luego creció a medida
-- que otras personas usaron más `tendsto`, y añadieron a la lista de
-- lemas útiles más lemas útiles a medida que usaban `tendsto` para
-- hacer otras cosas y luego abstraían propiedades que descubrieron que
-- eran útiles. Por ejemplo, esta semana (escribo esto en febrero de
-- 2021) Heather Macbeth estaba trabajando en formas modulares en Lean y
-- descubrió que necesitaba un lema sobre `tendsto`, que, después de
-- algunas discusión en el chat de Zulip Lean, Heather y yo nos dimos
-- cuenta de que era una declaración sobre cómo `tendsto` conmuta con un
-- cierto tipo de coproducto. Lo demostramos y Heather está ahora mismo
-- en proceso de añadirlo (`tendsto.prod_map_coprod`) a `mathlib`, la
-- biblioteca de matemáticas de Lean.
--
-- Debo señalar que nunca habría trabajado en ese problema con Heather
-- si no hubiera sido por el hecho de que le había estado enseñando
-- sobre filtros y, por lo tanto, ¡tenía que aprender sobre ellos como
-- es debido!
--
-- Volvamos a ver nuestra nueva prueba de `tendsto_mul`. La prueba se
-- desprende de dos lemas de 2 líneas. Yo te explicaré el primero, y tú
-- puedes experimentar con el segundo. Veamos el primero.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    is_limit a l ↔ tendsto a at_top (𝓝 l) :=
-- ---------------------------------------------------------------------

example
  (a : ℕ → ℝ)
  (l : ℝ)
  : is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_at_top,
  refl,
end

-- Las tripas de la primera es `metric.tendsto_at_top`, que es en
-- realidad una declaración sobre los espacios métricos. Dice que en
-- cualquier espacio métrico, la definición estándar del espacio métrico
-- épsilon-N de un límite de una secuencia es un caso especial de este
-- predicado de filtro `tendsto`. Aquí hay una prueba con más detalles
-- (`simp_rw` es sólo una versión ligeramente más versión de `rw` que
-- necesitamos por razones técnicas, porque `rw` no se ve bajo una
-- sentencia `∀`):

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    is_limit a l ↔ tendsto a at_top (𝓝 l)
-- ---------------------------------------------------------------------

-- Esta prueba más explícita utiliza la siguiente notación elegante
-- llamada "filter.eventually" :
--    `(∀ᶠ (x : α) en F, P x) ↔ {x : α | P x} ∈ F`
-- y entonces sólo se reduce a los siguientes dos hechos matemáticos
-- (aquí `ball l ε` es la bola abierta de radio `ε` centro `l` ), el
-- primero es `metric.tendsto_nhds` y el segundo `mem_at_top_sets`:
--    1) Si `a` está en un espacio métrico, entonces
--       `S ∈ 𝓝 l ↔ ∃ ε > 0, bola l ε ⊆ S`
--    2) Si `at_top` es el filtro sobre `ℕ` que vimos la última vez,
--       entonces `T ∈ at_top ↔ ∃ N : ℕ, {n : ℕ | N ≤ n} ⊆ T``
--
-- El resto es fácil, porque `tendsto a at_top (𝓝 l)` significa,
-- por definición de `tendsto`,
--    `∀ S : set ℝ, S ∈ 𝓝 l → a -¹' S ∈ at_top`
-- que se traduce en
--    `∀ S : set ℝ, (∃ ε > 0, ball l ⊆ S) → (∃ N, n ≥ N → a n ∈ S)`.
-- y si se despliega el envoltorio lógico se verá que esto no es más que
-- la definición habitual de `is_limit` (nótese que `a n ∈ ball l ε` es
-- definición es igual a `dist (a n) l < ε` que, para los reales, es
-- es igual a `|a n - l| < ε`).

-- Demostración:
--      is_limit a l
--    ↔ ∀ ε, ε > 0 → (∃ c, ∀ b , b ≥ c → b ∈ {x : ℕ | dist (a x) l < ε})
--         [por def. de límite]
--    ↔ ∀ ε, ε > 0 → {x | dist (a x) l < ε} ∈ at_top
--         [por mem_at_top_sets]
--    ↔ ∀ ε, ε > 0 → (∀ᶠ x in at_top, dist (a x) l < ε)
--         [por eventually_iff]
--    ↔ tendsto a at_top (𝓝 l)

example
  (a : ℕ → ℝ)
  (l : ℝ)
  : is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  simp_rw [metric.tendsto_nhds, eventually_iff, mem_at_top_sets],
  refl,
end

-- =====================================================================
-- § tendsto.mul                                                      --
-- =====================================================================

-- Veamos ahora el segundo ejemplo.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el límite del producto es el producto de los
-- límites.
-- ---------------------------------------------------------------------

example
  (a b : ℕ → ℝ)
  (l m : ℝ)
  (ha : is_limit a l)
  (hb : is_limit b m)
  : is_limit (a * b) (l * m) :=
begin
  rw is_limit_iff_tendsto at *,
  exact tendsto.mul ha hb,
end

-- Si pasas el ratón por encima de `tendsto.mul` en esa prueba, quizás
-- puedas distinguir que dice lo siguiente: si tenemos un espacio
-- topológico `M` con una multiplicación continua en él, y si `F` es un
-- filtro en `α` y `f` y `g` son aplicaciones `α → M`, entonces `tendsto
-- f F (𝓝 l)` y `tendsto g F (𝓝 m)` implica `tendsto a (f * g) F 𝓝 (l *
-- m)`. Aplicamos esto con `F` el filtro cofinito y ya hemos terminado,
-- usando que la multiplicación en ℝ es una función continua. ¿Cómo
-- sabía Lean esto? Pues, `[has_continuous_mul M]` estaba entre
-- corchetes así que eso significa que el sistema de inferencia de
-- clases de tipo se supone que se ocupa de ello. Vamos ver cómo se las
-- arregla con la afirmación de que la multiplicación es continua en los
-- reales.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la multiplicación es los reales es continua.
-- ---------------------------------------------------------------------

example : has_continuous_mul ℝ :=
begin
  apply_instance
end

-- La gente que definió `ℝ` en Lean hizo una definición, y el precio que
-- tuvieron que pagar para hacerla utilizable fue que tuvieron que hacer
-- una gran API para para demostrar que un conjunto acotado no vacío de
-- reales tiene un límite superior mínimo y que los reales eran un
-- anillo topológico (y por lo tanto la multiplicación era
-- continua). Pero este precio se pagó en 2018 por lo que los
-- matemáticos podemos ahora utilizar estos hechos de forma gratuita.
--

-- Todo lo que queda entonces, si queremos ver los detalles, es
-- demostrar `tendsto.mul`, y esto es una afirmación sobre filtros en
-- espacios topológicos, así que hagámoslo. Primero ¿qué significa
-- `continuo`?

-- =====================================================================
-- § Continuidad                                                      --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar X e Y como espacios topológicos y f : X → Y
-- ---------------------------------------------------------------------

variables (X Y : Type) [topological_space X] [topological_space Y]
variable  (f : X → Y)

-- Si `x : X`, ¿qué significa que `f` sea continua en `x`?
-- Intuitivamente, significa que si se mueve `x` una pequeña cantidad,
-- entonces `f x` se mueve en una pequeña cantidad. En otras palabras,
-- "f" envía un pequeño entorno de `x` a un pequeño entorno de `f x`.
--
-- Si nuestro modelo mental del filtro de entorno `𝓝 x` es una especie
-- de conjunto generalizado que corresponde a un entorno infinitesimal
-- de `x`, veremos por qué Lean tiene la siguiente definición de
-- "continuo":

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    continuous_at f x ↔ tendsto f (𝓝 x) (𝓝 (f x))
-- ---------------------------------------------------------------------

lemma continuous_at_def
  (x : X)
  : continuous_at f x ↔ tendsto f (𝓝 x) (𝓝 (f x)) :=
begin
  refl,
end

-- Es probable que te hayan dicho lo que significa que una función `f :
-- X → Y` entre espacios *métricos* sea continua en `x`. ¿Te han dicho
-- alguna vez lo que significa que una función entre espacios
-- "topológicos" sea continua en "x", en lugar de ser continua en todo
-- "X"? Este es lo que significa.
--
-- Ahora vamos a empezar con la prueba de `tendsto.mul`, construyendo
-- una API para la definición de `continuous_at`. No olvides cosas como
--    `tendsto_id : tendsto id x x`
-- `  tendsto.comp : tendsto g G H → tendsto f F G → tendsto (g ∘ f) F H`
-- de la orimera parte de este tema.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la identidad es continua en todos los
-- puntos.
-- ---------------------------------------------------------------------

example
  (x : X)
  : continuous_at id x :=
begin
  exact tendsto_id,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar Z como espacio topológico y g : Y → Z
-- ---------------------------------------------------------------------

variables (Z : Type) [topological_space Z]
variable  (g : Y → Z)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la composición de funciones continuas es
-- continua.
-- ---------------------------------------------------------------------

example
  (x : X)
  (hf : continuous_at f x)
  (hg : continuous_at g (f x))
  : continuous_at (g ∘ f) x :=
begin
  exact tendsto.comp hg hf,
end

-- Ahora demostramos un resultado clave, llamado `tendsto.prod_mk_nhds`.
--
-- Notación para el producto de tipos: si `Y` y `Z` son tipos, entonces
-- `Y × Z` es el producto de tipos, y la notación para un término
-- general es `(y, z) : Y × Z` con `y : Y` y `z : Z`.
--
-- Un caso especial del teorema siguiente es que si las aplicaciones
-- `f : X → Y` y `g : X → Z` son continuas en `x` entonces el producto
-- `f × g : X → Y × Z` es también continua en `x`. Vamos a demostrar
-- algo más general: si `α` es un tipo cualquiera y `F : filtro α` es
-- cualquier filtro, `y : Y`, `z : Z` y `f : α → Y` y `g : α → Z`
-- satisfacen `tendsto f F (𝓝 y)` y `tendsto g F (𝓝 z)`, entonces
-- `tendsto a (f × g) F (𝓝 (y,z))`, donde "f × g" es la 1a aplicación
-- `λ x, (f x, g x)`.
-- El dato clave que necesitarás de la API de topología del producto es
--    mem_nhds_prod_iff :
--      S ∈ 𝓝 ((a, b) : X × Y) ↔`
--      ∃ (U : set X) (H : U ∈ 𝓝 a) (V :set Y) (H : V ∈ 𝓝 b), U.prod V ⊆ S
-- Esto es todo lo que deberías necesitar sobre la topología del
-- producto (no vamos a entrar en cómo está definida la topología del
-- producto, pero el hecho clave dice matemáticamente que un entorno
-- de `(a,b) : X × Y` contiene un producto de entornos de `X` y de
-- `Y`).
--
-- También necesitarás saber
--    mk_mem_prod : a ∈ U → b ∈ V → (a, b) ∈ U.prod V
-- donde para `U : set X` y `V : set Y`, `U.prod V = prod U V` es el
-- subconjunto obvio de `X × Y`.
--
-- Recordemos también de primera la parte del tema:
--     mem_map : S ∈ map φ F ↔ {x : α | φ x ∈ S} ∈ F
--     tendsto_def : tendsto f F G ↔ ∀ (S : conjunto Y), S ∈ G → f -¹' S ∈ F
-- (aunque aquí hay una trampa: la definición real de
-- `tendsto f F G` es `∀ {S : set Y}, S ∈ G ...` )

-- #check tendsto_def

-- this is called `tendsto.prod_mk_nhds` in Lean but try proving it yourself.
example {α : Type} (f : α → Y) (g : α → Z) (x : X) (F : filter α) (y : Y) (z : Z)
  (hf : tendsto f F (𝓝 y)) (hg : tendsto g F (𝓝 z)) :
  tendsto (λ x, (f x, g x)) F (𝓝 (y, z)) :=
begin
  -- say `S` is a neighbourhood of `(y, z)`.
  rintro S hS,
  -- use the given fact about neighbourhoods of point in a product of top spaces
  rw mem_nhds_prod_iff at hS,
  -- to get neighbourhoods of `y` and `z`.
  rcases hS with ⟨U, hU, V, hV, h⟩,
  -- The goal is `S ∈ map ...` so use `mem_map`.
  rw mem_map,
  -- I claim {x : α | f x ∈ U} ∈ F
  have hfxU : {x : α | f x ∈ U} ∈ F := hf hU, -- technical note: I didn't
                                  -- rewrite `tendsto_def` so I don't supply `U`
  -- I claim {x : α | g x ∈ V} ∈ F
  have hgxV : {x : α | g x ∈ V} ∈ F := hg hV,
  -- so their intersection is in F
  have hfg := inter_mem_sets hfxU hgxV,
  -- and so it suffices to show that their intersection contains `{x : α | (f x, g x) ∈ S}`
  refine mem_sets_of_superset hfg _,
  -- but we just now take everything apart
  rintro x ⟨(hxf : f x ∈ U), (hxg : g x ∈ V)⟩,
  apply h,
  -- and apply mk_mem_prod
  exact set.mk_mem_prod hxf hxg,
end

-- Armed with `tendsto.prod_mk_nhds`, let's prove the version of `tendsto.mul`
-- which we need
lemma key_lemma {α M : Type} [topological_space M] [has_mul M]
  {f g : α → M} {F : filter α} {a b : M} (hf : tendsto f F (𝓝 a))
  (hg : tendsto g F (𝓝 b))
  (hcontinuous : continuous_at (λ (mn : M × M), mn.1 * mn.2) (a,b)) :
  tendsto (f * g) F (𝓝 (a * b)) :=
begin
  set f1 : M × M → M := λ mn, mn.1 * mn.2 with hf1,
  set f2 : α → M × M := λ x, (f x, g x) with hf2,
  have h1 : f1 ∘ f2 = f * g,
  { ext x,
    refl },
  have h2 : tendsto f2 F (𝓝 (a, b)) := tendsto.prod_mk_nhds hf hg,
  rw ← h1,
  apply tendsto.comp _ h2,
  apply hcontinuous,
end

-- The final ingredient is that multiplication is continuous on ℝ, which we
-- just take from the real API:
lemma real.continuous_mul_at (a b : ℝ) :
  continuous_at (λ xy : ℝ × ℝ, xy.1 * xy.2) (a, b) :=
begin
  -- it's in the library
  exact continuous.continuous_at real.continuous_mul,
end

-- and now we have all the ingredients we need for our own proof of `is_limit_mul`!
example  (a b : ℕ → ℝ) (l m : ℝ)
  (ha : is_limit a l) (hb : is_limit b m) :
  is_limit (a * b) (l * m) :=
begin
  rw is_limit_iff_tendsto at *,
  apply key_lemma ha hb,
  apply real.continuous_mul_at,
end
