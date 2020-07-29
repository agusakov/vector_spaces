import definitions

universes u v w

namespace vector_space

-- 1.) Prove that -(-v) = v for every v ∈ V
lemma neg_neg' (F : Type u) (α : Type v) [field F] [add_comm_group α] [vector_space F α] : 
    ∀ v : α, - (- v) = v :=
begin
    intro v,
    apply @add_right_cancel _ _ _ (-v),
    rw add_neg_self,
    rw neg_add_self,
end

-- 2.) Suppose a ∈ F, v ∈ V, and a • v = 0. Prove that a = 0 or v = 0.
lemma zero_or_zero (F : Type u) (α : Type v) [field F] [add_comm_group α] [vector_space F α] : 
    ∀ a : F, ∀ v : α, a • v = 0 → (a = 0) ∨ (v = 0) :=
begin
    intros a v hyp,
    sorry,
end

-- 3.) Suppose v, w ∈ V. Explain why there exists a unique x ∈ V such that v + 3x = w.

-- 4.) maybe skip this one

-- 5.) Show that in the definition of a vector space, the additive inverse condition can be replaced with the condition that 0v = 0 for all v ∈ V.

-- maybe replace add_comm_group with something else? idk
-- this works in just commutative groups, not just vector spaces.
-- simplify maybe? make it an instance of add_comm_group?
lemma zero_smul_zero_iff_add_inv (F : Type u) (α : Type v) [field F] [add_comm_group α] [vector_space F α] :
    (∀ v : α, (0 : F) • v = 0) ↔ (∀ x : α, ∃ y : α, x + y = 0) :=
begin 
    split,
    intro hyp,
    intro v,
    specialize hyp v,
    rw ← add_neg_self (1 : F) at hyp,
    rw add_smul at hyp,
    rw one_smul at hyp,
    rw ← hyp,
    use (((-1) : F) • v),
    sorry,
end