-- Teoría de grupos
-- =====================================================================

import tactic

-- Nota técnica: Trabajamos en un espacio de nombres `oculto` porque
-- Lean ya tiene `group`. Ahora nuestra definición de grupo se llamará
-- realmente `oculto.group`.

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombres
-- ---------------------------------------------------------------------

namespace oculto

-- =====================================================================
-- § Definición de grupo                                              --
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase `group` como una extensión de las clases
-- `has_mul`, `has_one` y `has_inv` que verifica las propiedades
--    asociativa               : ∀ (a b c : G), (a * b) * c = a * (b * c)
--    neutro por la izquierda  : ∀ (a : G), 1 * a = a
--    inverso por la izquierda : ∀ (a : G), a⁻¹ * a = 1
-- ---------------------------------------------------------------------

class group (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_assoc : ∀ (a b c : G), a * b * c = a * (b * c))
(one_mul : ∀ (a : G), 1 * a = a)
(mul_left_inv : ∀ (a : G), a⁻¹ * a = 1)

-- La forma de decir "sea G un grupo" ahora es `(G : Type) [group G]`

-- Formalmente, un término de tipo `grupo G` consta de
-- + la definición de una operación interna: * : G → G → G
-- + la definición de un elemento neutro: 1 : G
-- + la definición de una operación inversa: (⁻¹) : G → G
-- + la 3 pruebas de los 3 axiomas.

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombres `group`
-- ---------------------------------------------------------------------

namespace group

-- ---------------------------------------------------------------------
-- Ejercicio. Definir `G` como una variable sobre grupos.
-- ---------------------------------------------------------------------

variables {G : Type} [group G]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los grupos se cumple la propiedad
-- cancelativa por la izquierda
--    a * b = a * c → b = c
-- ---------------------------------------------------------------------

lemma mul_left_cancel
  (a b c : G)
  (Habac : a * b = a * c)
  : b = c :=
begin
 calc b = 1 * b         : by rw one_mul
    ... = (a⁻¹ * a) * b : by rw mul_left_inv
    ... = a⁻¹ * (a * b) : by rw mul_assoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_assoc
    ... = 1 * c         : by rw mul_left_inv
    ... = c             : by rw one_mul
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ∀ a x y : G, x = a⁻¹ * y → a * x = y
-- ---------------------------------------------------------------------

lemma mul_eq_of_eq_inv_mul
  {a x y : G}
  (h : x = a⁻¹ * y)
  : a * x = y :=
begin
  apply mul_left_cancel a⁻¹,
  rw ←mul_assoc,
  rw mul_left_inv,
  rwa one_mul,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir a, b, c, x e y como variables sobre G.
-- ---------------------------------------------------------------------

variables (a b c x y : G)

-- ---------------------------------------------------------------------
-- Ejercicio [KB-R11). Demostrar que 1 es neutro por la derecha; es
-- decir,
--    a * 1 = a
-- ---------------------------------------------------------------------

@[simp] theorem mul_one :
  a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_left_inv,
end

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R13). Demostrar que
--    a * a⁻¹ = 1
-- ---------------------------------------------------------------------

@[simp] theorem mul_right_inv :
  a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
end

-- =====================================================================
-- § Simplificador de Lean                                            --
-- =====================================================================

-- Un humano ve "a * a⁻¹" en la teoría de grupos y lo reemplaza
-- instantáneamente con "1".
--
-- Vamos a entrenar una IA simple llamada "simp" para que haga lo
-- mismo.
--
-- El simplificador de Lean `simp` es un "sistema de reescritura de
-- términos". Esto significa que si le enseñas un montón de teoremas de
-- la forma `A = B` o `P ↔ Q` (etiquetándolos con el atributo `@[simp]`)
-- y luego le das un objetivo complicado, como por ejemplo:
--    (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1
-- Lean intentará usar la táctica `rw` tanto como pueda, usando los
-- lemas que se les ha enseñado, en un intento de simplificar el
-- objetivo. Si se las arregla para resolverlo por completo, ¡entonces
-- genial! Si no es así, pero piensas que debería haberlo hecho, es
-- posible que tengas que etiquetar más lemas con `@[simp]`.
--
-- `simp` solo debe usarse para cerrar completamente los objetivos.
--
-- Ahora vamos a entrenar al simplificador para resolver el ejemplo
-- anterior (de hecho, estamos entrenándolo para reducir un elemento
-- arbitrario de un grupo libre en una forma normal única, por lo que
-- resolverá cualquier igualdad que sea verdadera para todos los grupos,
-- como en el ejemplo anterior).
--
-- Notal importante: El simplificador de Lean hace una serie de
-- reescrituras, cada una reemplazando algo con algo más simple. ¡Pero
-- el simplificador siempre reescribirá de izquierda a derecha! Si le
-- dice que `A = B` es un lema de simplificación, entonces reemplazará
-- las `A` por las `B`, pero nunca reemplazará las `B` por las `A`.
--
-- Si etiqueta una prueba de `A = B` con `@[simp]` y también etiqueta
-- una prueba de `B = A` con `@[simp]`, entonces el simplificador se
-- atascará en un bucle infinito cuando se encuentra con una "A".
--
-- La igualdad no debe considerarse aquí simétrica.
--
-- Dado que el simplificador funciona de izquierda a derecha, es
-- importante observar que si `A = B` es un lema de simplificación,
-- entonces `B` debería ser más simple que `A`.
--
-- No es una coincidencia que en los teoremas a continuación
--    `@[simp] theorem mul_one (a : G) : a * 1 = a`
--    `@[simp] theorem mul_right_inv (a : G) : a * a⁻¹ = 1`
-- el lado derecho es más simple que el lado izquierdo.
--
-- Sería un desastre etiquetar `a = a * 1` con la etiqueta
-- `@[simp]`. ¿Puedes ver por qué?
--
-- ¡Entrenemos el simplificador de Lean! Enseñémosle los axiomas de un
-- grupo a continuación. Ya hemos visto los axiomas, por lo que tenemos
-- que etiquetarlos con el atributo `@ [simp]`.

-- ---------------------------------------------------------------------
-- Ejercicio. Etiquetar como reglas de simplificación los axiomas
-- one_mul (KB-R1), mul_left_inv (KB-R2) y mul_assoc (KB-R3).
-- ---------------------------------------------------------------------

attribute [simp] one_mul mul_left_inv mul_assoc

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R4). Demostrar que
--    a⁻¹ * (a * b) = b
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  a⁻¹ * (a * b) = b :=
begin
  rw ← mul_assoc,
  simp,
end

-- 2ª demostración
@[simp] lemma inv_mul_cancel_left :
  a⁻¹ * (a * b) = b :=
begin
  rw ← mul_assoc,
  -- squeeze_simp,
  simp only [one_mul,
             mul_left_inv],
end

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R14). Demostrar que
--    a * (a⁻¹ * b) = b
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  a * (a⁻¹ * b) = b :=
begin
  rw ←mul_assoc,
  simp,
end

-- 2ª demostración
@[simp] lemma mul_inv_cancel_left :
  a * (a⁻¹ * b) = b :=
begin
  rw ←mul_assoc,
  -- squeeze_simp,
  simp only [one_mul,
             mul_right_inv],
end

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R17). Demostrar que
--    (a * b)⁻¹ = b⁻¹ * a⁻¹
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  simp,
end

-- 2ª demostración
@[simp] lemma inv_mul :
  (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  -- squeeze_simp,
  simp only [mul_assoc,
             mul_inv_cancel_left,
             mul_right_inv]
end

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R8). Demostrar que
--    (1 : G)⁻¹ = 1
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  (1 : G)⁻¹ = 1 :=
begin
  apply mul_left_cancel (1 : G),
  rw mul_right_inv,
  simp,
end

-- 1ª demostración
@[simp] lemma one_inv :
  (1 : G)⁻¹ = 1 :=
begin
  apply mul_left_cancel (1 : G),
  rw mul_right_inv,
  -- squeeze_simp,
  simp only [one_mul],
end

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R12). Demostrar que
--    (a ⁻¹) ⁻¹ = a
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  (a ⁻¹) ⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  simp,
end

-- 2ª demostración
@[simp] lemma inv_inv :
  (a ⁻¹) ⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  -- squeeze_simp,
  simp only [mul_right_inv,
             mul_left_inv],
end

-- La razón para elegir estos cinco lemas es https://bit.ly/2YyZdhi

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 :=
  by simp

-- 2ª demostración
example :
  (a * b) * 1⁻¹⁻¹ * b⁻¹ * (a⁻¹ * a⁻¹⁻¹⁻¹) * a = 1 :=
-- by squeeze_simp
by simp only [mul_one,
              mul_assoc,
              mul_right_inv,
              inv_inv,
              mul_left_inv]

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * c = b → a = b * c⁻¹
-- ---------------------------------------------------------------------

lemma eq_mul_inv_of_mul_eq
  {a b c : G}
  (h : a * c = b)
  : a = b * c⁻¹ :=
begin
  rw ← h,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    b * a = c → a = b⁻¹ * c
-- ---------------------------------------------------------------------

lemma eq_inv_mul_of_mul_eq
  {a b c : G}
  (h : b * a = c)
  : a = b⁻¹ * c :=
begin
  rw ← h,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * b = b ↔ a = 1
-- ---------------------------------------------------------------------

lemma mul_left_eq_self
  {a b : G}
  : a * b = b ↔ a = 1 :=
begin
  split,
  { intro h,
    replace h := eq_mul_inv_of_mul_eq h,
    simp [h] },
  { intro h,
    rw [h, one_mul] }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * b = a ↔ b = 1
-- ---------------------------------------------------------------------

lemma mul_right_eq_self
  {a b : G}
  : a * b = a ↔ b = 1 :=
begin
  split,
  { intro h,
    replace h := eq_inv_mul_of_mul_eq h,
    simp [h] },
  { rintro rfl,
    simp },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * b = 1 → a = b⁻¹
-- ---------------------------------------------------------------------

lemma eq_inv_of_mul_eq_one
  {a b : G}
  (h : a * b = 1)
  : a = b⁻¹ :=
begin
  convert eq_mul_inv_of_mul_eq h,
  simp,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * b = 1 → a⁻¹ = b
-- ---------------------------------------------------------------------

lemma inv_eq_of_mul_eq_one
  {a b : G}
  (h : a * b = 1)
  : a⁻¹ = b :=
begin
  replace h := eq_mul_inv_of_mul_eq h,
  simp [h],
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    ∀ x : G, e * x = x → e = 1
-- ---------------------------------------------------------------------

lemma unique_left_id {e : G} (h : ∀ x : G, e * x = x) : e = 1 :=
calc e = e * 1 : by rw mul_one
  ...  = 1     : by rw h 1

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * b = 1 → b = a⁻¹
-- ---------------------------------------------------------------------

lemma unique_right_inv
  {a b : G}
  (h : a * b = 1)
  : b = a⁻¹ :=
begin
  apply mul_left_cancel a,
  simp [h],
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a * x = a * y ↔ x = y
-- ---------------------------------------------------------------------

lemma mul_left_cancel_iff
  (a x y : G)
  : a * x = a * y ↔ x = y :=
begin
  split,
  { apply mul_left_cancel, },
  { intro hxy,
    rwa hxy, },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    x * a = y * a → x = y
-- ---------------------------------------------------------------------

lemma mul_right_cancel
  (a x y : G)
  (Habac : x * a = y * a)
  : x = y :=
calc x = x * 1         : by rw mul_one
  ...  = x * (a * a⁻¹) : by rw mul_right_inv
  ...  = x * a * a⁻¹   : by rw mul_assoc
  ...  = y * a * a⁻¹   : by rw Habac
  ...  = y * (a * a⁻¹) : by rw mul_assoc
  ...  = y * 1         : by rw mul_right_inv
  ...  = y             : by rw mul_one

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a⁻¹ = b⁻¹ ↔ a = b
-- ---------------------------------------------------------------------

@[simp] theorem inv_inj_iff
  {a b : G}
  : a⁻¹ = b⁻¹ ↔ a = b :=
begin
  split,
  { intro h,
    rw [← inv_inv a, h, inv_inv b], },
  { rintro rfl,
    refl }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    a⁻¹ = b ↔ b⁻¹ = a
-- ---------------------------------------------------------------------

theorem inv_eq
  {a b : G}
  : a⁻¹ = b ↔ b⁻¹ = a :=
begin
  split;
  { rintro rfl,
    rw inv_inv }
end

end group

end oculto

-- =====================================================================
-- § Referencias                                                      --
-- =====================================================================

-- + Kevin Buzzard. "Formalising mathematics : workshop 2 — groups and
--   subgroups. https://bit.ly/3iaYdqM
-- + Kevin Buzzard. formalising-mathematics: week 2, Part_A_groups.lean
--   https://bit.ly/2WGkyoy
-- + Kevin Buzzard. formalising-mathematics: week 2, Part_A_groups_solutions.lean
--   https://bit.ly/3le1WGc
