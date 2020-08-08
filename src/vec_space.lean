import algebra.field
import algebra.module

universes u v w x

--class has_scalar (F : Type u) (α : Type v) := (smul : F → α → α)

--infixr ` • `:73 := has_scalar.smul

-- modules for a ring
class vec_space (F : Type u) (α : Type v) [field F] [add_comm_group α] 
extends has_scalar F α :=
(smul_add : ∀ (r : F) (x y : α), r • (x + y) = r • x + r • y)
(add_smul : ∀(r s : F) (x : α), (r + s) • x = r • x + s • x)
(mul_smul : ∀ (r s : F) (x : α), (r * s) • x = r • s • x)
(one_smul : ∀ x : α, (1 : F) • x = x)

instance set_functions (F : Type u) (S : Type v) [field F] : add_comm_group (S → F) :=
{ add := λ f g, λ x, f x + g x, -- (f + g)(x) = f(x) + g(x)
  add_assoc := λ a b c, funext (λ x, add_assoc _ _ _),
  zero := λ x, (0 : F),
  zero_add := λ a, funext (λ x, zero_add (a x)),
  add_zero := λ a, funext (λ x, add_zero (a x)),
  neg := λ a, λ x, -(a x),
  add_left_neg := λ a, funext (λ x, neg_add_self (a x)),
  add_comm := λ a b, funext (λ x, add_comm (a x) (b x))}

instance vec_space_pi (F : Type u) (S : Type v) [field F] : vec_space F (S → F) :=
{ smul := λ a, λ f, λ x, a * (f x),
  smul_add := λ a, λ f g, funext (λ x, mul_add a (f x) (g x)),
  add_smul := λ a b, λ f, funext (λ x, add_mul a b (f x)),
  mul_smul := λ a b, λ f, funext (λ x, mul_assoc a b (f x)),
  one_smul := λ f, funext (λ x, one_mul (f x)) 
}

lemma unique_add_id (α : Type v) [add_comm_group α] : 
    ∀ x : α, (∀ b : α, x + b = b) → x = 0 :=
begin
    intros x hyp,
    specialize hyp 0,
    rw eq_comm at hyp,
    rw hyp,
    symmetry,
    exact add_zero x,
end

lemma unique_add_inv (α : Type v) [add_comm_group α] : 
    ∀ x y : α, x + y = 0 → y = - x :=
begin
    intros x y hyp,
    rw ← neg_add_self x at hyp,
    rw add_comm (-x) x at hyp,
    exact add_left_cancel hyp,
end

lemma zero_smul_zero (F : Type u) (α : Type v) [field F] [add_comm_group α] [vec_space F α] :
    ∀ v : α, (0 : F) • v = 0 :=
begin
    intro v, -- 0 • v = 0 -> 0 • v + v = v -> 0 • v + 1 • v = v -> (0 + 1) • v = v -> 1 • v = v
    apply @add_right_cancel _ _ _ v,
    rw ← vec_space.one_smul v,
    rw ← vec_space.mul_smul,
    rw zero_mul,
    rw ← vec_space.add_smul,
    rw [zero_add, zero_add],
end

#check add_comm_group.neg

lemma neg_one_mul' (F : Type u) (α : Type v) [field F] [add_comm_group α] [vec_space F α] :
    ∀ v : α, ((-1) : F) • v = - v :=
begin
    intro v,
    apply @add_right_cancel _ _ _ v,
    rw ← vec_space.one_smul v,
    rw ← vec_space.mul_smul,
    rw neg_add_self,
    rw neg_one_mul,
    rw ← vec_space.add_smul,
    rw neg_add_self,
    apply zero_smul_zero,
end

lemma smul_zero_zero (F : Type u) (α : Type v) [field F] [add_comm_group α] [vec_space F α] :
    ∀ a : F, a • (0 : α) = 0 :=
begin
    intro a,
    have hyp : (0 : α) = (a • 0) + - (a • 0) := by rw add_neg_self (a • (0 : α)),
    conv_rhs {rw hyp},
    rw ← neg_one_mul' F _ (a • (0 : α)),
    rw ← vec_space.mul_smul,
    rw mul_comm,
    rw vec_space.mul_smul,
    rw ← vec_space.smul_add,
    rw neg_one_mul',
    rw add_neg_self,
end