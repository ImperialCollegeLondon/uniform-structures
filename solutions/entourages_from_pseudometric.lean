-- import the definitions of uniform space via entourages
import uniform_structure.entourages




-- import the definition of pseudometric space
import pseudometric_space

-- In this exercise we will show that a pseudometric on a set X 
-- gives rise to a collection of entourages for X 

-- This is a question about pseudometrics so let's put it
-- in the pseudometric namespace
open_locale classical
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
  intro x,
  have hx : d x x = 0,
    exact d_self d x,
  obtain ⟨ε, hε, hεU⟩ := hU,
  apply hεU,
  rw hx,
  linarith,
  
  
end

-- Axiom 2: anything bigger than an entourage is an entourage
lemma bigger (U V : set (X × X)) (hU : U ∈ entourages d) (hUV : U ⊆ V) :
  V ∈ entourages d :=
begin
  rw mem_entourages,
  obtain ⟨ε, hε, hεU⟩ := hU,
  use ε,
  split,
  apply hε,
  tauto,

end

-- Axiom 3: Intersection of two entourages is an entourage
lemma inter (U V : set (X × X)) (hU : U ∈ entourages d) (hV : V ∈ entourages d) :
  U ∩ V ∈ entourages d :=
begin
  rw mem_entourages,
  obtain ⟨ε1, hε1, hε1U⟩ := hU,
  obtain ⟨ε2, hε2, hε2V⟩ := hV,
  set e := min ε1 ε2 with he,
  use e,
  split,
  have h: e>0,
  simp,
  split,
  apply hε1,
  apply hε2,
  simp,
  split,
  apply hε1,
  apply hε2,
  simp,
  tauto,

end

/-

-/
-- Axiom 4: the "square root" axiom. 
-- You'll need `mem_comp_ent` here (defined in the entourages file)
lemma comp (U : set (X × X)) (hU : U ∈ entourages d) :
 ∃ (V : set (X × X)) (H : V ∈ entourages d), V ∘ V ⊆ U :=
begin
  obtain ⟨ε, hε, hεU⟩ := hU,
  use {z : X × X | d z.1 z.2 ≤ ε/2},
  split,
  rw mem_entourages,
  use ε/2,
  split,
  linarith,
  tauto,
  intro x,
  intro h,
  have q: d x.1 x.2 ≤ ε,
  have s: ∃ z, (x.1, z) ∈ {z : X × X | d z.1 z.2 ≤ ε/2} ∧ (z, x.2) ∈ {z : X × X | d z.1 z.2 ≤ ε/2},
  rw ← mem_comp_ent,
  apply h,
  obtain ⟨z, hz1, hz2⟩ := s,
  have p1: d x.1 z ≤ ε/2,
  apply hz1,
  have p2: d z x.2 ≤ ε/2,
  apply hz2,
  have p3 : d x.1 x.2 ≤ d x.1 z + d z x.2,
  apply d_triangle d,
  linarith,
  have p4: (x.1, x.2) ∈ U,
  apply hεU,
  apply q,
  cases x,
  apply p4,
end

-- Axiom 5: the "transpose" axiom.
lemma symm (U : set (X × X)) (hU : U ∈ entourages d) :
  {z : X × X | (z.snd, z.fst) ∈ U} ∈ entourages d :=
begin
  rw mem_entourages,
  obtain ⟨ε, hε, hεU⟩ := hU,
  use ε,
  split,
  apply hε,
  intros x y,
  have hx : d x y = d y x,
    exact d_comm d x y,
  intro h,
  apply hεU,
  have q:  d x y = d (x, y).snd (x, y).fst,
    apply hx,
  linarith,
end
 
definition to_entourages : uniform_space_entourage X :=
{ entourages := entourages d,
  refl := refl d,
  bigger := bigger d,
  inter := inter d,
  comp := comp d,
  symm := symm d }

end pseudometric
