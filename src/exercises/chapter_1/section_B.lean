import definitions

universes u v w

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