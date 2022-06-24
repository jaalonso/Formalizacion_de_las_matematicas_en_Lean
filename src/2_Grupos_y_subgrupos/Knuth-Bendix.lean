import tactic

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la clase `grupo` como una extensión de las clases
-- `has_mul`, `has_one` y `has_inv` que verifica las propiedades
--    asociativa               : ∀ (a b c : G), (a * b) * c = a * (b * c)
--    neutro por la izquierda  : ∀ (a : G), 1 * a = a
--    inverso por la izquierda : ∀ (a : G), a⁻¹ * a = 1
-- ---------------------------------------------------------------------

class grupo (G : Type) extends has_mul G, has_one G, has_inv G :=
(mul_asoc : ∀ (a b c : G), (a * b) * c = a * (b * c))
(uno_mul : ∀ (a : G), 1 * a = a)
(mul_inv_izq : ∀ (a : G), a⁻¹ * a = 1)

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombres `grupo`
-- ---------------------------------------------------------------------

namespace grupo

-- ---------------------------------------------------------------------
-- Ejercicio. Definir `G` como una variable sobre grupos.
-- ---------------------------------------------------------------------

variables {G : Type} [grupo G]

-- ---------------------------------------------------------------------
-- Ejercicio. Etiquetar como reglas de simplificación los axiomas
-- one_mul (KB-R1), mul_left_inv (KB-R2) y mul_assoc (KB-R3).
-- ---------------------------------------------------------------------

attribute [simp] uno_mul mul_inv_izq mul_asoc

-- ---------------------------------------------------------------------
-- Ejercicio. Definir a, b, c, x e y como variables sobre G.
-- ---------------------------------------------------------------------

variables (a b c x y : G)

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R4). Demostrar que
--    a⁻¹ * (a * b) = b
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  a⁻¹ * (a * b) = b :=
begin
  rw ← mul_asoc,
  simp,
end

-- 2ª demostración
@[simp]
lemma inv_mul_cancel_left :
  a⁻¹ * (a * b) = b :=
begin
  rw ← mul_asoc,
  -- squeeze_simp,
  simp only [uno_mul,
             mul_inv_izq],
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que en los grupos se cumple la propiedad
-- cancelativa por la izquierda
--    a * b = a * c → b = c
-- ---------------------------------------------------------------------

lemma mul_left_cancel
  (Habac : a * b = a * c)
  : b = c :=
begin
 calc b = 1 * b         : by rw uno_mul
    ... = (a⁻¹ * a) * b : by rw mul_inv_izq
    ... = a⁻¹ * (a * b) : by rw mul_asoc
    ... = a⁻¹ * (a * c) : by rw Habac
    ... = (a⁻¹ * a) * c : by rw mul_asoc
    ... = 1 * c         : by rw mul_inv_izq
    ... = c             : by rw uno_mul
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
  rw ← mul_asoc,
  rw mul_inv_izq,
  rwa uno_mul,
end

-- ---------------------------------------------------------------------
-- Ejercicio [KB-R11). Demostrar que 1 es neutro por la derecha; es
-- decir,
--    a * 1 = a
-- ---------------------------------------------------------------------

@[simp] theorem mul_one :
  a * 1 = a :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_inv_izq,
end

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R13). Demostrar que
--    a * a⁻¹ = 1
-- ---------------------------------------------------------------------

@[simp]
theorem mul_right_inv :
  a * a⁻¹ = 1 :=
begin
  apply mul_eq_of_eq_inv_mul,
  rw mul_one,
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
@[simp]
lemma one_inv :
  (1 : G)⁻¹ = 1 :=
begin
  apply mul_left_cancel (1 : G),
  rw mul_right_inv,
  -- squeeze_simp,
  simp only [uno_mul],
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
@[simp]
lemma inv_inv :
  (a ⁻¹) ⁻¹ = a :=
begin
  apply mul_left_cancel a⁻¹,
  -- squeeze_simp,
  simp only [mul_right_inv,
             mul_inv_izq],
end

-- ---------------------------------------------------------------------
-- Ejercicio (KB-R14). Demostrar que
--    a * (a⁻¹ * b) = b
-- ---------------------------------------------------------------------

-- 1ª demostración
example :
  a * (a⁻¹ * b) = b :=
begin
  rw ← mul_asoc,
  simp,
end

-- 2ª demostración
@[simp] lemma mul_inv_cancel_left :
  a * (a⁻¹ * b) = b :=
begin
  rw ← mul_asoc,
  -- squeeze_simp,
  simp only [uno_mul,
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
@[simp]
lemma inv_mul :
  (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
begin
  apply mul_left_cancel (a * b),
  rw mul_right_inv,
  -- squeeze_simp,
  simp only [mul_asoc,
             mul_inv_cancel_left,
             mul_right_inv]
end

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
              mul_asoc,
              mul_right_inv,
              inv_inv,
              mul_inv_izq]

-- ---------------------------------------------------------------------
-- Ejercicio. Cerrar el espacio de nombres `grupo`
-- ---------------------------------------------------------------------

end grupo
