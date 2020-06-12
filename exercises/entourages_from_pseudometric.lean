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

-- this lemma is true by definition
lemma mem_entourages (U : set (X × X)) :
  U ∈ entourages d ↔ ∃ ε > 0, ∀ x y : X, d x y ≤ ε → (x,y) ∈ U := iff.rfl 

-- The exerise is to show that the 5 axioms of a uniform space are
-- satisfied.

-- Hint: You can `rw mem_entourages` to change from `U ∈ entourages d` to the
-- explicit epsilon definition.

-- Hint: if `hU : U ∈ entourages d` then `obtain ⟨ε, hε, hεU⟩ := hU` will
-- get you the ε which is a witness to U being an entourage for d.

-- Axiom 1: the diagonal is in U
lemma refl (U : set (X × X)) (hU : U ∈ entourages d) :
  ∀ (x : X), (x, x) ∈ U :=
begin
  rw mem_entourages at hU,
  obtain ⟨ε, hε, hεU⟩ := hU,
  intro x,
  apply hεU,
  rw d_self d,
  linarith
end

lemma refl' (U : set (X × X)) (hU : U ∈ entourages d) :
  ∀ (x : X), (x, x) ∈ U :=
begin
  intro x,
  have hx : d x x = 0,
    exact d_self d x,
  obtain ⟨ε, hε, hεU⟩ := hU,
  apply hεU,
  rw hx,
  linarith
end


-- Axiom 2: anything bigger than an entourage is an entourage
lemma bigger (U V : set (X × X)) (hU : U ∈ entourages d) (hUV : U ⊆ V) :
  V ∈ entourages d :=
begin
  obtain ⟨ε, hε, hεU⟩ := hU,
  rw mem_entourages,
  use ε,
  use hε,
  intros x y hxy,
  apply hUV,
  apply hεU,
  assumption,
end

-- Axiom 3: Intersection of two entourages is an entourage
lemma inter (U V : set (X × X)) (hU : U ∈ entourages d) (hV : V ∈ entourages d) :
  U ∩ V ∈ entourages d :=
begin
  rw mem_entourages at ⊢ hU hV,
  obtain ⟨ε₁, hε₁, hε₁U⟩ := hU,
  obtain ⟨ε₂, hε₂, hε₂V⟩ := hV,
  use (min ε₁ ε₂),
  split, apply lt_min; assumption,
  intros x y hxy,
  rw le_min_iff at hxy,
  split,
  { apply hε₁U,
    exact hxy.1
  },
  { apply hε₂V,
    exact hxy.2
  }
end

-- Axiom 4: the "square root" axiom. 
-- You'll need `mem_comp_ent` here (defined in the entourages file)
lemma comp (U : set (X × X)) (hU : U ∈ entourages d) :
 ∃ (V : set (X × X)) (H : V ∈ entourages d), V ∘ V ⊆ U :=
begin
  obtain ⟨ε, hε, hεU⟩ := hU,
  use {z : X × X | d z.1 z.2 ≤ ε/2},
  split, use ε/2, split, linarith, intros, assumption,
  rintro ⟨x,y⟩ h,
  apply hεU,
  rw mem_comp_ent at h,
  rcases h with ⟨z, hxz, hzy⟩,
  dsimp at *, 
  calc d x y ≤ d x z + d z y : d_triangle d x z y
    ...      ≤ ε : by linarith [hxz, hzy]
end

-- Axiom 5: the "transpose" axiom.
lemma symm (U : set (X × X)) (hU : U ∈ entourages d) :
  {z : X × X | (z.snd, z.fst) ∈ U} ∈ entourages d :=
begin
  obtain ⟨ε, hε, hεU⟩ := hU,
  use [ε, hε],
  intros x y hxy,
  apply hεU,
  convert hxy using 1,
  exact d_comm d y x
end
 
definition to_entourages : uniform_space_entourage X :=
{ entourages := entourages d,
  refl := refl d,
  bigger := bigger d,
  inter := inter d,
  comp := comp d,
  symm := symm d }

end pseudometric