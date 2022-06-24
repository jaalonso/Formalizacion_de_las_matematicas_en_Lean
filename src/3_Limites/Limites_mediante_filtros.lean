-- Límites mediante filtros
-- =====================================================================

-- ---------------------------------------------------------------------
-- Ejercicio. Importar las teorías
-- + Limites_de_sucesiones
-- + topology.instances.real
-- ---------------------------------------------------------------------

import .Limites_de_sucesiones
import topology.instances.real

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el espacio de nombres `filter`.
-- ---------------------------------------------------------------------

open filter

-- ---------------------------------------------------------------------
-- Ejercicio. Abrir el contexto `topological_space`
-- ---------------------------------------------------------------------

open_locale topological_space

-- ---------------------------------------------------------------------
-- Ejercicio. Iniciar el espacio de nombres `oculto`-
-- ---------------------------------------------------------------------

namespace oculto

-- ---------------------------------------------------------------------
-- Ejercicio. Demostrar
-- ---------------------------------------------------------------------

lemma is_limit_iff_tendsto
  (a : ℕ → ℝ)
  (l : ℝ)
  : is_limit a l ↔ tendsto a at_top (𝓝 l) :=
begin
  rw metric.tendsto_at_top,
  congr',
end

-- this is `is_limit_add`

example
  (a b : ℕ → ℝ)
  (l m : ℝ)
  : is_limit a l → is_limit b m → is_limit (a + b) (l + m) :=
begin
  repeat {rw is_limit_iff_tendsto},
  exact tendsto.add,
end

-- this is `is_limit_mul`

example
  (a b : ℕ → ℝ)
  (l m : ℝ)
  : is_limit a l → is_limit b m → is_limit (a * b) (l * m) :=
begin
  repeat {rw is_limit_iff_tendsto},
  exact tendsto.mul,
end

end oculto
