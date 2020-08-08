import .vec_space
import group_theory.subgroup
import data.finset
import algebra.big_operators
import algebra.pointwise
--import ring_theory.polynomial.basic

open_locale big_operators classical


namespace vec_space

universes u v w x

open subgroup

structure subspace (F : Type u) (α : Type v) [field F] [add_comm_group α] [vec_space F α] extends add_subgroup α :=
(smul_mem : ∀ (a : F) {x}, x ∈ carrier → a • x ∈ carrier)

namespace subspace

variables (F : Type u) (α : Type v) [field F] [add_comm_group α] [vec_space F α] (β : subspace F α)

--instance : has_coe_t (subspace F β) (set β) := ⟨λ s, s.carrier⟩
instance : has_coe (subspace F α) (add_subgroup α) := { coe := subspace.to_add_subgroup }


/-instance : has_coe_t (subspace F β) (set β) := ⟨λ s, s.carrier⟩
instance : has_mem M (submodule R M) := ⟨λ x p, x ∈ (p : set M)⟩
instance : has_coe_to_sort (submodule R M) := ⟨_, λ p, {x : M // x ∈ p}⟩


instance : has_add β := ⟨λx y, ⟨x.1 + y.1, add_mem _ x.2 y.2⟩⟩
instance : has_zero p := ⟨⟨0, zero_mem _⟩⟩
instance : inhabited p := ⟨0⟩
instance : has_scalar R p := ⟨λ c x, ⟨c • x.1, smul_mem _ c x.2⟩⟩-/

/-begin
    intros a b,
    refine ⟨a • b, _⟩, 
    exact subspace.smul_mem β a b.2, -- b.2 proving that a thing is a subtype
end,-/

instance to_vec_space (F : Type u) (α : Type v) [field F] [add_comm_group α] [vec_space F α](β : subspace F α) : vec_space F β :=
{ smul := λ a b, ⟨a • b, β.smul_mem a b.2⟩,
  smul_add := λ r a b, subtype.eq (vec_space.smul_add r a b),
  add_smul := λ r s a, subtype.eq (vec_space.add_smul r s a),
  mul_smul := λ r s a, subtype.eq (vec_space.mul_smul r s a),
  one_smul := λ a, subtype.eq (vec_space.one_smul a) }

lemma sum_mem_sum (S : finset (subspace F α)) (f : subspace F α → α)
  (hf : ∀ x ∈ S, f x ∈ x.carrier) : 
  (∑ x in S, f x) ∈ (∑ x in S, x : set α) :=
begin
    -- ∀ Uᵢ ∈ {U₁, ..., U_m}, f(x) ∈ Uᵢ
    -- u₁ + ... + u_m ∈ U₁ + ... + U_m
    revert hf,
    apply finset.induction_on S,
    rw finset.sum_empty,
    rw finset.sum_empty,
    intro hyp,
    exact set.zero_mem_zero,
    intros β s hyp IH hyp2,
    rw finset.forall_mem_insert at hyp2,
    cases hyp2 with hyp2 hyp3,
    rw finset.sum_insert hyp,
    rw finset.sum_insert hyp,
    apply set.add_mem_add,
    exact hyp2,
    apply IH,
    exact hyp3,
    --sorry,
end

/-lemma sum_mem_sum' (S : finset (subspace F α)) (u : α)
  (hu : u ∈ (∑ x in S, x : set α)) : 
  ∃ (f : subspace F α → α), (∀ x ∈ S, f x ∈ x.carrier) ∧ u = (∑ x in S, f x) :=
begin -- u ∈ U₁ + ... + U_m then u = ∑ uᵢ for uᵢ ∈ Uᵢ
-- ∀ Uᵢ, ∃ uᵢ s.t. 
    revert hu,
    revert u,
    apply finset.induction_on S,
    rw finset.sum_empty,
    --rw finset.sum_empty,
    intros u hyp3,
    use λ x, 0,
    split,
    intros x hyp2,
    exact add_subgroup.zero_mem x,

    rw finset.sum_const_zero,
    rw set.mem_zero at hyp3,
    exact hyp3,

    intros a s hyp2 IH u hyp3,
    rw finset.sum_insert hyp2 at hyp3,
    rw set.mem_add at hyp3,
    rcases hyp3 with ⟨b, c, hyp3, hyp4, hyp5⟩,
    specialize IH c hyp4,
    refine ⟨_, _, _⟩,
    intro d,
    use b, -- function that maps a to b
    --intros x hyp6,
    intros x hyp7,
    rw finset.mem_insert,
    --have hyp7 : if x ∈ s then f x else b,
    --if x ∈ s then f x else b, if_pos, if_neg
end-/


/-def subspace_sum (S : finset (subspace F α)) : subspace F α := 
{
  carrier := ∑ x in S, x,
  --{y | ∃ f : (Π x : subspace F α, x ∈ S → x), (∑ x in S.attach, f x x.2 : α) = y} , 
  -- {u₁ + ... + u_m : u₁ ∈ U₁, ..., u_m ∈ U_m}
  zero_mem' := 
  begin
    convert sum_mem_sum F α S (λ x, 0) (λ x hyp, add_subgroup.zero_mem x),
    rw finset.sum_const_zero,
  end,
  add_mem' := λ a b hyp hyp2, _,
  neg_mem' := _,
  smul_mem := _ }-/

/-def add (s : finset (subspace F α)) : subspace F α :=
{y | ∃ (f : Π (i : (↑s : set (subspace F α))), i), y = ∑ x in (↑s : set (subspace F α)), f x}-/

end subspace

end vec_space