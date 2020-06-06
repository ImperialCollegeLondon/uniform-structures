import tactic

/-!

# The entourage definition of a uniform space

We start with a little section on `U ∘ V` (see axiom 4 of the wikipedia
entourage definition of a uniform space)

We then give the entourage definition of a uniform space

-/

section comp_rel -- composing relations

/-- composition `∘` of two subsets of X × X -/
def comp_rel {X : Type} (U V : set (X×X)) :=
  {p : X × X | ∃z : X, (p.1, z) ∈ U ∧ (z, p.2) ∈ V}

notation U ` ∘ ` V := comp_rel U V

variables {X : Type} {U V : set (X × X)} {x y : X}

/-- This is the theorem which gives the defining property of U ∘ V -/
@[simp] theorem mem_comp_rel :
  (x, y) ∈ U ∘ V ↔ ∃ z, (x, z) ∈ U ∧ (z, y) ∈ V := iff.rfl -- true by definition

end comp_rel -- that should be all we need

structure uniform_space_entourage (X : Type) :=
(entourages : set (set (X × X)))
-- now go through the five axioms in Wikipedia
(refl : ∀ U ∈ entourages, ∀ x : X, (x,x) ∈ U)
(bigger : ∀ U V : set (X × X), U ∈ entourages → U ⊆ V → V ∈ entourages)
(inter : ∀ U V ∈ entourages, U ∩ V ∈ entourages)
(comp : ∀ U ∈ entourages, ∃ V ∈ entourages, V ∘ V ⊆ U)
(symm : ∀ U ∈ entourages, {z : X × X | prod.swap z ∈ U} ∈ entourages)

