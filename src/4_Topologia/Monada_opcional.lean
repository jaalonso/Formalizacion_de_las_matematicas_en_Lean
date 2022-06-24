-- ---------------------------------------------------------------------
-- Ejercicio. Importar la librería de tácticas.
-- ---------------------------------------------------------------------

import tactic

-- Nota. La mónada opcional está definida por
--    inductive option (α : Type u)
--    | none         : option
--    | some (x : α) : option

-- Nota. Para cada tipo `X` la función `some : X → option X` es
-- inyectiva.
--    some_injective (α : Type*) : function.injective (@some α)
-- que es un corolario de
--    some_inj {a b : α} : some a = some b ↔ a = b

-- Nota. Los elementos opcionales son distintos de none:
--    some_ne_none (x : α) : some x ≠ none

-- Nota: Para definir una función `option X → Y` hay que definir un
-- elemento de `Y` para cada `some x` con `x : X` y también un elemento
-- de `Y`para `none` goes. Se puede definir con el recursor de `option`,
-- llamado `option.rec`,
--    Π {α : Type u} {C : option α → Sort l},
--      C none → (Π (val : α), C (some val)) → Π (n : option α), C n

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar X e Y como variables sobre tipos.
-- ---------------------------------------------------------------------

variables {X Y : Type}

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    g : Y → (X → Y) → (option X → Y)
-- tal que (g y f) es la función que asigna
-- + y a none y
-- + (f x) a (some x).
-- ---------------------------------------------------------------------

def g : Y → (X → Y) → option X → Y :=
λ y f, λ t, option.rec y f t

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar
-- + f como una variable para funciones de X en Y.
-- + x como una variable sobre X.
-- + y como una variable sobre Y.
-- ---------------------------------------------------------------------

variable (f : X → Y)
variable (x : X)
variable (y : Y)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (g y f) none
-- ---------------------------------------------------------------------

example :
  (g y f) none = y :=
begin
  refl
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    (g y f) (some x) = f x
-- ---------------------------------------------------------------------

example :
  (g y f) (some x) = f x :=
begin
  refl
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir
--    option_func : (X → Y) → (option X → option Y) :=
-- tal que (option_func f) es el functor correspondiente a f.
-- ---------------------------------------------------------------------

def option_func : (X → Y) → (option X → option Y) :=
λ f, λ t, option.rec none (some ∘ f) t

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que que option_func verifica el axioma de los
-- functores para la identidad.
-- ---------------------------------------------------------------------

lemma option_id
  (ox : option X)
  : option_func id ox = ox :=
begin
  cases ox with x,
  { refl },
  { refl }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Declarar Z como una variable de tipos.
-- ---------------------------------------------------------------------

variable (Z : Type)

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que que option_func verifica el axioma de los
-- functores para la composición
-- ---------------------------------------------------------------------

lemma option_comp
  (f : X → Y)
  (g : Y → Z)
  (ox : option X) :
  option_func (g ∘ f) ox = (option_func g) (option_func f ox) :=
begin
  cases ox with x,
  { refl },
  { refl },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    eta : X → option X
-- como la función some.
-- ---------------------------------------------------------------------

def eta : X → option X :=
some

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la función eta es una transformación
-- natural.
-- ---------------------------------------------------------------------

lemma eta_nat
  (f : X → Y)
  (x : X)
  : option_func f (eta x) = eta (f x) :=
begin
  refl,
end

-- ---------------------------------------------------------------------
-- Ejercicio. Definir la función
--    mu : option (option X) → option X
-- que transforma `none` en `none` y `some ox` en `ox`.
-- ---------------------------------------------------------------------

def mu : option (option X) → option X :=
λ t, option.rec none id t

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que la función mu es una transformación
-- natural.
-- ---------------------------------------------------------------------

lemma mu_nat (
  f : X → Y)
  (oox : option (option X))
  : option_func f (mu oox) = mu (option_func (option_func f) oox) :=
begin
  cases oox,
  { refl },
  { refl }
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    mu ((option_func mu) ooox) = mu (mu ooox)
-- ---------------------------------------------------------------------

lemma coherence1
  (ooox : option (option (option X)))
  : mu ((option_func mu) ooox) = mu (mu ooox) :=
begin
  cases ooox,
  { refl },
  { refl },
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    mu (eta ox) = ox
-- ---------------------------------------------------------------------

lemma coherence2a
  (ox : option X)
  : mu (eta ox) = ox :=
begin
  refl
end

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar que
--    mu (option_func eta ox) = ox
-- ---------------------------------------------------------------------

lemma coherence2b
  (ox : option X)
  : mu (option_func eta ox) = ox :=
begin
  cases ox,
  { refl },
  { refl },
end
