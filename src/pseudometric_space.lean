import topology.metric_space.baire

#check metric_space

/-!

# Pseudometric spaces

A pseudometric on a set is a distance function obeying
all the axioms of a metric except possible d(x,y)=0 ↔ x = y.

-/

-- `has_dist X` just means "X has a distance function called `dist`"

/-- A pseudometric space is a metric space without the axiom that d(x,y)=0 -> x=y -/ 
class pseudometric_space (X : Type) extends has_dist X :=
(dist_self : ∀ x : X, dist x x = 0)
(dist_comm : ∀ x y : X, dist x y = dist y x)
(dist_triangle : ∀ x y z : X, dist x z ≤ dist x y + dist y z)

-- fun fact: we never included the axiom that dist x y ≥ 0, because it follows
-- from the other axioms!

namespace pseudometric_space

variables (X : Type) [pseudometric_space X]

theorem dist_nonneg {x y : X} : 0 ≤ dist x y :=
begin

  -- First note 0 = d(x,x) ≤ d(x,y)+d(y,x) = 2d(x,y)

  have h2 : 0 ≤ 2 * dist x y,
    calc 0 = dist x x : by rw dist_self
    ...    ≤ dist x y + dist y x : dist_triangle x y x
    ...    = dist x y + dist x y : by rw dist_comm
    ...    = 2 * dist x y : by ring,

  -- and now the result is obvious

  linarith
end

end pseudometric_space

