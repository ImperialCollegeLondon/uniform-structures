-- import the definitions of uniform space via entourages
import uniform_structure.entourages

-- import the definition of pseudometric space
import pseudometric_space

-- In this exercise we will show that a pseudometric on a set X 
-- gives rise to a collection of entourages for X 

-- This is a question about pseudometrics so let's put it
-- in the pseudometric namespace

namespace pseudometric

-- Let X be a set (or a type), and let d be a pseudometric on X
variables {X : Type} (d : X → X → ℝ) [is_pseudometric d]

-- Define U ⊆ X × X to be an entourage if there exists ε > 0 such
-- that d(x,y)≤ε → (x,y) ∈ U

def entourages :=
  {U : set (X × X) | ∃ ε > 0, ∀ x y : X, d x y ≤ ε → (x,y) ∈ U}

-- The exerise is to show that the 5 axioms of a uniform space are
-- satisfied.

lemma refl (U : set (X × X)) (hU : U ∈ entourages d) :
  ∀ (x : X), (x, x) ∈ U :=
begin
  sorry
end

lemma bigger (U V : set (X × X)) (hU : U ∈ entourages d) (hUV : U ⊆ V) :
  V ∈ entourages d :=
begin
  sorry
end

lemma inter (U V : set (X × X)) (hU : U ∈ entourages d) (hV : V ∈ entourages d) :
  U ∩ V ∈ entourages d :=
begin
  sorry
end

-- hint: this is a triangle inequality proof so ε/2 might be helpful
lemma comp (U : set (X × X)) (hU : U ∈ entourages d) :
 ∃ (V : set (X × X)) (H : V ∈ entourages d), V ∘ V ⊆ U :=
begin
  sorry
end

lemma symm (U : set (X × X)) (hU : U ∈ entourages d) :
  {z : X × X | (z.snd, z.fst) ∈ U} ∈ entourages d :=
begin
  sorry
end
 
definition to_entourages : uniform_space_entourage X :=
{ entourages := entourages d,
  refl := refl d,
  bigger := bigger d,
  inter := inter d,
  comp := comp d,
  symm := symm d }

end pseudometric