import MIL.Common
import Mathlib.GroupTheory.QuotientGroup.Basic

set_option autoImplicit true


@[ext]
structure Submonoid₁ (M : Type) [Monoid M] where
  /-- The carrier of a submonoid. -/
  carrier : Set M
  /-- The product of two elements of a submonoid belongs to the submonoid. -/
  mul_mem {a b} : a ∈ carrier → b ∈ carrier → a * b ∈ carrier
  /-- The unit element belongs to the submonoid. -/
  one_mem : 1 ∈ carrier

/-- Submonoids in `M` can be seen as sets in `M`. -/
instance [Monoid M] : SetLike (Submonoid₁ M) M where
  coe := Submonoid₁.carrier
  coe_injective' _ _ := Submonoid₁.ext



example [Monoid M] (N : Submonoid₁ M) : 1 ∈ N := N.one_mem

example [Monoid M] (N : Submonoid₁ M) (α : Type) (f : M → α) := f '' N


example [Monoid M] (N : Submonoid₁ M) (x : N) : (x : M) ∈ N := x.property


instance SubMonoid₁Monoid [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun x y ↦ ⟨x*y, N.mul_mem x.property y.property⟩
  mul_assoc := fun x y z ↦ SetCoe.ext (mul_assoc (x : M) y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun x ↦ SetCoe.ext (one_mul (x : M))
  mul_one := fun x ↦ SetCoe.ext (mul_one (x : M))


example [Monoid M] (N : Submonoid₁ M) : Monoid N where
  mul := fun ⟨x, hx⟩ ⟨y, hy⟩ ↦ ⟨x*y, N.mul_mem hx hy⟩
  mul_assoc := fun ⟨x, _⟩ ⟨y, _⟩ ⟨z, _⟩ ↦ SetCoe.ext (mul_assoc x y z)
  one := ⟨1, N.one_mem⟩
  one_mul := fun ⟨x, _⟩ ↦ SetCoe.ext (one_mul x)
  mul_one := fun ⟨x, _⟩ ↦ SetCoe.ext (mul_one x)


class SubmonoidClass₁ (S : Type) (M : Type) [Monoid M] [SetLike S M] : Prop where
  mul_mem : ∀ (s : S) {a b : M}, a ∈ s → b ∈ s → a * b ∈ s
  one_mem : ∀ s : S, 1 ∈ s

instance [Monoid M] : SubmonoidClass₁ (Submonoid₁ M) M where
  mul_mem := Submonoid₁.mul_mem
  one_mem := Submonoid₁.one_mem


instance [Monoid M] : Min (Submonoid₁ M) :=
  ⟨fun S₁ S₂ ↦
    { carrier := S₁ ∩ S₂
      one_mem := ⟨S₁.one_mem, S₂.one_mem⟩
      mul_mem := fun ⟨hx, hx'⟩ ⟨hy, hy'⟩ ↦ ⟨S₁.mul_mem hx hy, S₂.mul_mem hx' hy'⟩ }⟩


example [Monoid M] (N P : Submonoid₁ M) : Submonoid₁ M := N


def Submonoid.Setoid [CommMonoid M] (N : Submonoid M) : Setoid M  where
  r := fun x y ↦ ∃ w ∈ N, ∃ z ∈ N, x*w = y*z
  iseqv := {
    refl := fun x ↦ ⟨1, N.one_mem, 1, N.one_mem, rfl⟩
    symm := fun ⟨w, hw, z, hz, h⟩ ↦ ⟨z, hz, w, hw, h.symm⟩
    trans := by
      rintro a b c
      rintro ⟨w, hw, z, hz, h⟩
      rintro ⟨w', hw', z', hz', h'⟩
      -- I actually did this out of order, so read the portion for mul that i write later
      -- its alot of text, you cant miss it
      use w * w'
      use N.mul_mem hw hw'
      use z * z'
      use N.mul_mem hz hz'
      rw [← mul_assoc a w w']
      rw [h]
      rw [mul_comm b z]
      rw [mul_assoc z b w']
      rw [h']
      rw [mul_comm z (c * z')]
      rw [mul_assoc c z' z]
      rw [mul_comm z' z]
  }

instance [CommMonoid M] : HasQuotient M (Submonoid M) where
  quotient' := fun N ↦ Quotient N.Setoid

def QuotientMonoid.mk [CommMonoid M] (N : Submonoid M) : M → M ⧸ N := Quotient.mk N.Setoid

set_option linter.unusedTactic false

instance [CommMonoid M] (N : Submonoid M) : Monoid (M ⧸ N) where
  mul := Quotient.map₂ (· * ·) (by
    rintro a₁ b₁
    rintro ⟨w, hw, z, hz, ha⟩
    rintro a₂ b₂
    rintro ⟨w', hw', z', hz', hb⟩
    simp
    -- Note that ha includes w and hb includes w', so lets introduce those into this equation
    -- we say that there exists a Z where a₁ * a₂ * (w * w') = b₁ * b₂ * z
    use w*w'
    -- However, we have to prove that w * w' is inside Submonoid M in the first place
    #check hw
    #check hw'
    -- we can prove this because a submonoid is closed under multiplication, and both w and w'
    -- are members of N as per hw and hw' (Submonoid M)
    #check N.mul_mem
    #check N.mul_mem hw
    #check N.mul_mem hw hw'
    use N.mul_mem hw hw'

    -- now we are left to prove that there exists a z also inside N

    -- like before, we can note that ha includes z and hb includes z'
    -- so lets introduce them as z itself
    use z*z'
    -- same as before, we need to prove that z * z' ∈ N
    #check hz
    #check hz'
    use N.mul_mem hz hz'

    -- Now we can get started on some rewrites and such to get it to a place we want :)
    -- We can see that hb is looking for a₂ * w', so lets switch w and w'
    rw [mul_comm w w']
    -- now lets get the parenthesis in the right spots to do the replace with hb
    rw [← mul_assoc (a₁ * a₂) w' w]
    rw [mul_assoc a₁ a₂ w']
    rw [hb]
    -- now we want to turn the remaining a₁ and w into a b₁ and z
    -- and we can see that ha does just that, so lets reorder some things
    rw [mul_comm a₁ (b₂ * z')]
    rw [mul_assoc (b₂ * z') a₁ w]
    rw [ha]
    -- and lastly, we just need to reoder it to be the same as the right :)
    rw [mul_comm (b₂ * z') (b₁ * z)]
    rw [mul_assoc b₁ z (b₂ * z')]
    rw [mul_comm z (b₂ * z')]
    rw [mul_assoc b₂ z' z]
    rw [mul_comm z' z]
    rw [← mul_assoc b₁ b₂ (z * z')]
  )
  mul_assoc := by
    rintro ⟨a⟩ ⟨b⟩ ⟨c⟩
    apply Quotient.sound
    simp
    rw [mul_assoc a b c]
    apply @Setoid.refl M N.Setoid
  one := by
    apply QuotientMonoid.mk N 1
  one_mul := by
    rintro ⟨a⟩
    apply @Quotient.sound
    simp
  mul_one := by
    rintro ⟨a⟩
    apply Quotient.sound
    simp
