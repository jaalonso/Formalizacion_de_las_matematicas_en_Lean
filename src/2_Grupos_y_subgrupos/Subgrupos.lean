-- Subgrupos
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Importar la teoría de grupos de la sesión anterior.
-- ---------------------------------------------------------------------


import .Grupos

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombre `oculto`.
-- ---------------------------------------------------------------------

namespace oculto

-- ---------------------------------------------------------------------
-- Ejercicio. Un subgrupo de un grupo G es un subconjunto de G que
-- contiene al elemento neutro y es cerrado por la multiplicación y el
-- inverso. Definir la estructura `subgroup` tal que `subgroup G` es el
-- tipo de los subgrupos de G.
-- ---------------------------------------------------------------------

structure subgroup (G : Type) [group G] :=
(carrier : set G)
(one_mem' : (1 : G) ∈ carrier)
(mul_mem' {x y} : x ∈ carrier → y ∈ carrier → x * y ∈ carrier)
(inv_mem' {x} : x ∈ carrier → x⁻¹ ∈ carrier)

/-

Pdte. Traducir carrier por elementos.
Pdte. Usar notación funcional en lugar de la de punto.


At this point, here's what we have.

A term `H` of type `subgroup G`, written `H : subgroup G`, is a
*quadruple*. To give a term `H : subgroup G` is to give the following four things:
1) `H.carrier`  (a subset of `G`),
2) `H.one_mem'` (a proof that `1 ∈ H.carrier`),
3) `H.mul_mem'` (a proof that `H` is closed under multiplication)
4) `H.inv_mem'` (a proof that `H` is closed under inverses).

Note in particular that Lean, being super-pedantic, *distinguishes* between
the subgroup `H` and the subset `H.carrier`. One is a subgroup, one is
a subset. When we get going we will start by setting up some infrastructure
so that this difference will be hard to notice.

Note also that if `x` is in the subgroup `H` of `H` then the _type_ of `x` is still `G`,
and `x ∈ carrier` is a Proposition. Note also that `x : carrier` doesn't
make sense (`carrier` is a term, not a type, rather counterintuitively).

-/

-- ---------------------------------------------------------------------
-- Ejercicio. Iniciar el espacio de nombres subgroup.
-- ---------------------------------------------------------------------

namespace subgroup

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombres `oculto.group`
-- ---------------------------------------------------------------------

open oculto.group

-- ---------------------------------------------------------------------
-- Ejercicio. Definir las siguientes variables
-- + G para grupos y
-- + H, J y K para subgrupos de G.
-- ---------------------------------------------------------------------

variables {G : Type} [group G]
variables (H J K : subgroup G)

-- La notación `h ∈ H.carrier` no es correcta. Además, no quiero
-- escribir "H.carrier" en todas partes; lo que quiero es poder
-- identificar el subgrupo `H` con el conjunto de sus elementos
-- (`H.carrier`).
--
-- Hay que tener en cuenta que estas cosas no son iguales, en primer
-- lugar porque `H` contiene la prueba de que `H.carrier` es un
-- subgrupo, y en segundo lugar, porque tienen diferentes tipos: `H`
-- tiene el tipo `supgroup G` y `H.carrier` tiene el tipo `set G`.

-- ---------------------------------------------------------------------
-- Ejercicio. Sean `x : G` y `H : subgroup G`. Definir la notación
-- `x ∈ H` para denotar `x ∈ H.carrier`.
-- ---------------------------------------------------------------------

instance : has_mem G (subgroup G) := ⟨λ y H, y ∈ H.carrier⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Sean `x : G` y `H : subgroup G`. Definir la notación
-- `↑H` para denotar `H.carrier`.
-- ---------------------------------------------------------------------

instance : has_coe (subgroup G) (set G) := ⟨λ H, H.carrier⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Sea `g : G`. Demostrar que
--    g ∈ H.carrier ↔ g ∈ H
-- ---------------------------------------------------------------------

@[simp] lemma mem_carrier
  {g : G}
  : g ∈ H.carrier ↔ g ∈ H :=
by refl

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que `g` está en `H` considerado como un
-- subconjunto de `G` syss` g` está en `H` considerado como subgrupo de
-- `G`.
-- ---------------------------------------------------------------------

@[simp] lemma mem_coe
  {g : G}
  : g ∈ (↑H : set G) ↔ g ∈ H :=
by refl

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    1 ∈ H
-- ---------------------------------------------------------------------

theorem one_mem :
  (1 : G) ∈ H :=
one_mem' H

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los subgrupos son cerrados respecto de las
-- multiplicaciones.
-- ---------------------------------------------------------------------

theorem mul_mem
  {x y : G}
  : x ∈ H → y ∈ H → x * y ∈ H :=
mul_mem' H

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los subgrupos son cerrados respecto de los
-- inversos.
-- ---------------------------------------------------------------------

theorem inv_mem {x : G} : x ∈ H → x⁻¹ ∈ H :=
inv_mem' H

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    x⁻¹ ∈ H ↔ x ∈ H
-- ---------------------------------------------------------------------

@[simp] theorem inv_mem_iff
  {x : G}
  : x⁻¹ ∈ H ↔ x ∈ H :=
begin
  split,
  { intro h,
    rw ← oculto.group.inv_inv x,
    exact inv_mem H h, },
  { exact inv_mem H, },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si `x` y `xy` están en `H`, entonces `y`
-- también lo está.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  {x y : G}
  (hx : x ∈ H)
  (hxy : x * y ∈ H)
  : y ∈ H :=
begin
  replace hx : x⁻¹ ∈ H := inv_mem H hx,
  have hy : x⁻¹ * (x * y) ∈ H := mul_mem H hx hxy,
  simp at hy,
  exact hy,
end

-- 2ª demostración
theorem mem_of_mem_mul_mem
  {x y : G}
  (hx : x ∈ H)
  (hxy : x * y ∈ H)
  : y ∈ H :=
begin
  rw ← inv_mem_iff at hx,
  convert mul_mem H hx hxy,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si dos subgrupos de G tienen los mismos
-- elementos, entonces son iguales.
-- ---------------------------------------------------------------------

-- 1ª demostración
example
  {H K : subgroup G}
  (h : H.carrier = K.carrier)
  : H = K :=
begin
  cases H,
  cases K,
  simp at h,
  simp,
  exact h,
end

-- 2ª demostración
theorem ext'
  {H K : subgroup G}
  (h : H.carrier = K.carrier)
  : H = K :=
begin
  cases H,
  cases K,
  simp * at *,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que dos subgrupos son iguales syss tienen los
-- mismos elementos.
-- ---------------------------------------------------------------------

theorem ext'_iff
  {H K : subgroup G}
  : H.carrier = K.carrier ↔ H = K :=
begin
  split,
  { exact ext', },
  { intro h,
    rw h, }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si dos subgrupos tienen los mismos
-- elementos, entonces son iguales.
-- ---------------------------------------------------------------------

@[ext] theorem ext
  {H K : subgroup G}
  (h : ∀ x, x ∈ H ↔ x ∈ K)
  : H = K :=
begin
  apply ext',
  ext,
  apply h,
end

-- Etiquetamos ese teorema con `ext` para que la táctica `ext` funcione
-- en subgrupos; es decir, para demostrar que dos subgrupos son iguales
-- se puede usar la táctica `ext` para reducirlo a demostrar que tienen
-- los mismos elementos.


-- =====================================================================
-- § La estructura de retículo de subgrupos                           --
-- =====================================================================

-- Los subgrupos de un grupo forman lo que se conoce como un retículo;
-- es decir, es un conjunto parcialmente ordenado con una las funciones
-- max y min.
--
-- Se ordenan parcialmente los subgrupos diciendo `H ≤ K` si
-- `H.carrier ⊆ K.carrier`.
--
-- Los subgrupos incluso tienen las funciones Sup e Inf (el Inf de de
-- los subgrupos de un grupo es su intersección; su Sup es el subgrupo
-- generado por su unión).
--
-- Esta estructura (un conjunto parcialmente ordenado con Sup e Inf) se
-- denomina "retículo completo", y Lean tiene esta estructura
-- definida
--
-- Nosotros construiremos una estructura de retículo completo en los
-- subgrupos del grupo G. Comenzamos por definiendo una relación ≤ sobre
-- el tipo de los subgrupos de un grupo: Decimos `H ≤ K` si
-- `H.carrier ⊆ K.carrier`.


-- ---------------------------------------------------------------------
-- Ejercicio. Definir la relación ≤ sobre el tipo de los subgrupos del
-- grupo G de forma que `H ≤ K` si `H.carrier ⊆ K.carrier`.
-- ---------------------------------------------------------------------

instance : has_le (subgroup G) := ⟨λ H K, H.carrier ⊆ K.carrier⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    H ≤ K ↔ H.carrier ⊆ K.carrier
-- ---------------------------------------------------------------------

lemma le_def :
  H ≤ K ↔ H.carrier ⊆ K.carrier :=
by refl

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    H ≤ K ↔ ∀ g, g ∈ H → g ∈ K
-- ---------------------------------------------------------------------

lemma le_iff :
  H ≤ K ↔ ∀ g, g ∈ H → g ∈ K :=
by refl

-- Nota: En los siguientes ejercicios se demostrará que ≤ es un orden
-- parcial.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    H ≤ H
-- ---------------------------------------------------------------------

@[refl] lemma le_refl :
  H ≤ H :=
by rw le_def

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    H ≤ K → K ≤ H → H = K
-- ---------------------------------------------------------------------

lemma le_antisymm :
  H ≤ K → K ≤ H → H = K :=
begin
  rw [le_def, le_def, ← ext'_iff],
  exact set.subset.antisymm,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    H ≤ J → J ≤ K → H ≤ K
-- ---------------------------------------------------------------------

@[trans] lemma le_trans :
  H ≤ J → J ≤ K → H ≤ K :=
begin
  rw [le_def, le_def, le_def],
  exact set.subset.trans,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los subgrupos de G con la relación ≤ es un
-- orden parcial.
-- ---------------------------------------------------------------------

instance : partial_order (subgroup G) :=
{ le          := (≤),
  le_refl     := le_refl,
  le_antisymm := le_antisymm,
  le_trans    := le_trans }

-- =====================================================================
-- § Intersecciones                                                   --
-- =====================================================================

-- Demostremos que la intersección de dos subgrupos es un subgrupo. En
-- Lean esta es su definición: dados dos subgrupos, definimos un nuevo
-- subgrupo cuyo subconjunto subyacente es la intersección de los
-- subconjuntos, y luego probamos los axiomas.

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    inf : subgroup G → subgroup G → subgroup G
-- tal que (inf H K) es el subgrupo intersección de H y de K.
-- ---------------------------------------------------------------------

-- 1ª solución
def inf (H K : subgroup G) : subgroup G :=
{ carrier := H.carrier ∩ K.carrier,
  one_mem' :=
    begin
      split,
      { exact one_mem H, },
      { exact one_mem K, },
    end,
  mul_mem' :=
    begin
      intros x y hx hy,
      cases hx with hxH hxK,
      cases hy with hyH hyK,
      split,
      { exact mul_mem H hxH hyH },
      { exact mul_mem K hxK hyK },
    end,
  inv_mem' :=
    begin
      rintro x ⟨hxH, hxK⟩,
      exact ⟨inv_mem H hxH, inv_mem K hxK⟩,
    end }

-- 2ª solución
def inf_term_mode (H K : subgroup G) : subgroup G :=
{ carrier  := carrier H ∩ carrier K,
  one_mem' := ⟨one_mem H,
               one_mem K⟩,
  mul_mem' := λ _ _ ⟨hhx, hkx⟩ ⟨hhy, hky⟩,
              ⟨mul_mem H hhx hhy,
               mul_mem K hkx hky⟩,
  inv_mem' := λ x ⟨hhx, hhy⟩,
              ⟨inv_mem H hhx,
               inv_mem K hhy⟩}

-- ---------------------------------------------------------------------
-- Ejercicio. Asignar el símbolo ⊓ a la operación inf.
-- ---------------------------------------------------------------------

instance : has_inf (subgroup G) := ⟨inf⟩

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que el conjunto subyacente de la intersección de
-- dos subgrupos es la intersección de los conjuntos subyacentes.
-- ---------------------------------------------------------------------

lemma inf_def
  (H K : subgroup G)
  : (H ⊓ K : set G) = (H : set G) ∩ K :=
by refl

-- =====================================================================
-- § Subgrupo generado por un subconjunto                             --
-- =====================================================================

-- Definir el sup de dos subgrupos es más difícil, porque no solo
-- tomamos la unión, tenemos que mirar el subgrupo generado por esta
-- unión. Así que necesitamos definir el subgrupo de `G` generado por un
-- subconjunto `S: set G`. Hay dos formas completamente diferentes de
-- hacer esto. La primera es "de arriba hacia abajo" (podríamos definir
-- el subgrupo generado por `S` como la intersección de todos los
-- subgrupos de `G` que contienen a `S`. La segunda es "de abajo hacia
-- arriba" (podríamos definir el subgrupo generado por `S` por inducción
-- diciendo que `S` está en el subgrupo, 1 está en el subgrupo, el
-- producto de dos cosas en el subgrupo está en el subgrupo, el inverso
-- de algo en el subgrupo está en el subgrupo, y eso es todo). Ambos
-- métodos funcionan bastante bien en Lean. Vamos a utilizar el primero.

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombres `set`.
-- ---------------------------------------------------------------------

open set

/-

Here is the API for `set.bInter` (or `bInter`, as we can now call it):

Notation: `⋂` (type with `\I`)

If `X : set (subgroup G)`, i.e. if `X` is a set of subgroups of `G`, then

`⋂ K ∈ X, (K : set G)` means "take the intersection of the underlying subsets".

-- mem_bInter_iff says you're in the intersection iff you're in
-- all the things you're intersecting. Very useful for rewriting.
`mem_bInter_iff : (g ∈ ⋂ (K ∈ S), f K) ↔ (∀ K, K ∈ s → g ∈ f K)`

-- mem_bInter is just the one way implication. Very useful for `apply`ing.
`mem_bInter : (∀ K, K ∈ s → g ∈ f K) → (g ∈ ⋂ (K ∈ S), f K)`



-/
/-
We will consider the closure of a set as the intersect of all subgroups
containing the set
-/

#check mem_bInter_iff
#check mem_bInter

-- Se usarán las siguientes propiedades de la intersección de familias
-- de conjuntos: Sean s : set α, t : α → set β, y : β. Entonces
--    mem_bInter_iff : y ∈ (⋂ x ∈ s, t x) ↔ ∀ x ∈ s, y ∈ t x
--    mem_bInter     : (∀ x ∈ s, y ∈ t x) → y ∈ ⋂ x ∈ s, t x

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    Inf : set (subgroup G) → subgroup G
-- tal que (Inf X) es la intersección de conjunto X de sugrupos de G.
-- ---------------------------------------------------------------------

-- 1ª solución:
def Inf (X : set (subgroup G)) : subgroup G :=
{ carrier := ⋂ K ∈ X, (K : set G),
  one_mem' :=
    begin
      apply mem_bInter,
      intros H hH,
      apply one_mem H,
    end,
  mul_mem' :=
    begin
      intros x y hx hy,
      rw mem_bInter_iff at *,
      intros H hH,
      apply mul_mem H,
      { apply hx,
        exact hH },
      { exact hy H hH }
    end,
  inv_mem' :=
    begin
      intros x hX,
      rw mem_bInter_iff at *,
      intros H hH,
      exact inv_mem H (hX H hH),
    end,
}

-- 2ª solución
def Inf' (X : set (subgroup G)) : subgroup G :=
{ carrier  := ⋂ t ∈ X, (t : set G),
  one_mem' := mem_bInter (λ i h, one_mem i),
  mul_mem' := λ x y hx hy,
              mem_bInter (λ i h, mul_mem i (by apply mem_bInter_iff.1 hx i h)
                                           (by apply mem_bInter_iff.1 hy i h)),
  inv_mem' := λ x hx,
              mem_bInter (λ i h, inv_mem i (by apply mem_bInter_iff.1 hx i h)) }

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    closure : set G → subgroup G
-- tal que (closure S) es la clausura de S; es decir, el menor subgrupo
-- de G que contiene a S.
-- ---------------------------------------------------------------------

def closure (S : set G) : subgroup G :=
  Inf {H : subgroup G | S ⊆ H}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    x ∈ closure S ↔ ∀ H : subgroup G, S ⊆ H → x ∈ H
-- ---------------------------------------------------------------------

lemma mem_closure_iff
  {S : set G}
  {x : G}
  : x ∈ closure S ↔ ∀ H : subgroup G, S ⊆ H → x ∈ H :=
mem_bInter_iff

-- Un operador de clausura en un conjunto S es una función cl del
-- conjunto potencia de S en sí mismo que satisface las siguientes
-- condiciones para todos los subconjuntos X, Y de S:
--    1) X ⊆ cl X
--    2) X ⊆ Y → cl X ⊆ cl Y
--    3) cl (cl X) = cl X
--
-- Vamos a demostrar que closure es un operador de clausura.

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    S ⊆ ↑(closure S)
-- ---------------------------------------------------------------------

-- 1ª demostración
lemma subset_closure
  (S : set G)
  : S ⊆ ↑(closure S) :=
begin
  intro g,
  intro hgS,
  rw [mem_coe, mem_closure_iff],
  intros H hH,
  apply hH,
  exact hgS,
end

-- 2ª demostración
lemma subset_closure'
  (S : set G)
  : S ⊆ closure S :=
λ s hs H ⟨y, hy⟩, by {rw [←hy, mem_Inter], exact λ hS, hS hs}

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que si S ⊆ T, entonces closure S ≤ closure T.
-- ---------------------------------------------------------------------

lemma closure_mono
  {S T : set G}
  (hST : S ⊆ T)
  : closure S ≤ closure T :=
begin
  intros x hx,
  rw [mem_carrier, mem_closure_iff] at *,
  intros H hTH,
  apply hx,
  exact subset.trans hST hTH,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    closure S ≤ H ↔ S ⊆ ↑H
-- ---------------------------------------------------------------------

lemma closure_le
  (S : set G)
  (H : subgroup G)
  : closure S ≤ H ↔ S ⊆ ↑H :=
begin
  split,
  { intro hSH,
    exact subset.trans (subset_closure S) hSH },
  { intros hSH g hg,
    rw [mem_carrier, mem_closure_iff] at hg,
    exact hg _ hSH }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    closure S = closure (closure S)
-- ---------------------------------------------------------------------

lemma closure_closure
  (S : set G)
  : closure S = closure (closure S) :=
begin
  apply le_antisymm,
  { apply subset_closure, },
  { rw closure_le,
    intros x hx,
    exact hx },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    closure ↑H = H
-- ---------------------------------------------------------------------

lemma closure_self
  {H : subgroup G}
  : closure ↑H = H :=
begin
  apply le_antisymm,
  { rw le_iff,
    intro g,
    rw mem_closure_iff,
    intro h,
    apply h,
    refl },
  { exact subset_closure H }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Sean G un grupo, S ⊆ G y p una propiedad sobre
-- G. Demostrar que si
--    ∀ x ∈ S, p x
--    p 1
--    ∀ x y, p x → p y → p (x * y)
--    ∀ x, p x → p x⁻¹
-- entonces
--    ∀ x, x ∈ closure S → p x
-- ---------------------------------------------------------------------

-- 1ª demostración
lemma closure_induction
  {p : G → Prop}
  {S : set G}
  (HS : ∀ x ∈ S, p x)
  (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (Hinv : ∀ x, p x → p x⁻¹)
  : ∀ x, x ∈ closure S → p x :=
begin
  let H : subgroup G :=
  { carrier  := p,
    one_mem' := H1,
    mul_mem' := Hmul,
    inv_mem' := Hinv },
  change closure S ≤ H,
  change S ⊆ ↑H at HS,
  rw closure_le,
  exact HS,
end

-- 2ª demostración
lemma closure_induction'
  {p : G → Prop}
  {S : set G}
  (HS : ∀ x ∈ S, p x)
  (H1 : p 1)
  (Hmul : ∀ x y, p x → p y → p (x * y))
  (Hinv : ∀ x, p x → p x⁻¹)
  : ∀ x, x ∈ closure S → p x :=
λ x h, (@closure_le _ _ _ ⟨p, H1, Hmul, Hinv⟩).2 HS h

-- Una conexión de Galois https://bit.ly/3vfzFSS entre un par de tipos α
-- y β, parcialmente ordenados, es un par de funciones `l : α → β` y
-- `u : β → α` tales que `∀a b, l a ≤ b ↔ a ≤ u b`. Su definición en
-- Lean es
--    def galois_connection [preorder α] [preorder β] (l : α → β) (u : β → α) :=
--      ∀a b, l a ≤ b ↔ a ≤ u b
--
-- A inserción de Galois insertion es una conexión de Galois connection
-- tal que `l ∘ u = id`. También contiene una función de elección. Su
-- definición en Lean es
--    structure galois_insertion {α β : Type*} [preorder α] [preorder β] (l : α → β) (u : β → α) :=
--    (choice : Πx:α, u (l x) ≤ x → β)
--    (gc : galois_connection l u)
--    (le_l_u : ∀x, x ≤ l (u x))
--    (choice_eq : ∀a h, choice a h = l a)


-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que `closure : set G → subgroup G` y
-- `coe : subgroup G → set G` forman una conexión de Galois entre los
-- subgrupos de G.
-- ---------------------------------------------------------------------

lemma gc :
  galois_connection (closure : set G → subgroup G) (coe : subgroup G → set G) :=
closure_le

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que `closure : set G → subgroup G` y
-- `coe : subgroup G → set G` forman una inserción de Galois entre los
-- subgrupos de G.
-- ---------------------------------------------------------------------

def gi : galois_insertion (closure : set G → subgroup G) (coe : subgroup G → set G) :=
{ choice := λ S _, closure S,
  gc := gc,
  le_l_u := λ H, subset_closure (H : set G),
  choice_eq := λ _ _, rfl }

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que los subgrupos son un retículo completo.
-- ---------------------------------------------------------------------

instance : complete_lattice (subgroup G) :=
{.. galois_insertion.lift_complete_lattice gi}

end subgroup

end oculto

-- =====================================================================
-- § Referencias                                                      --
-- =====================================================================

-- + Kevin Buzzard. "Formalising mathematics : workshop 2 — groups and
--   subgroups. https://bit.ly/3iaYdqM
-- + Kevin Buzzard. formalising-mathematics: week 2, Part_B_subgroups.lean
--   https://bit.ly/3oWT9ux
-- + Kevin Buzzard. formalising-mathematics: week 2, Part_B_subgroups_solutions.lean
--   https://bit.ly/3iR1z2z
