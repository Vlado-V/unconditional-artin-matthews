module

public import ArtinMatthews.PrincipalOppositeFourier


set_option backward.privateInPublic true
@[expose] public section

/-! Exact fibers of reduction from R/(ab) to R/(b).  Multiplication by
b identifies the kernel with R/(a), without a coprimality hypothesis. -/
namespace ArtinMatthews.SIntegerFourier

open scoped Classical
noncomputable section
variable {R : Type*} [CommRing R] [IsDomain R]

def oppositeKernelScale (a b : R) :
    (R ⧸ Ideal.span {a}) →+ (oppositeReduction a b).toAddMonoidHom.ker where
  toFun x := ⟨quotientScale a b x, by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    change Ideal.Quotient.mk (Ideal.span {b}) (b * x) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton.mpr ⟨x, rfl⟩)⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' x y := Subtype.ext (map_add _ x y)

theorem oppositeKernelScale_bijective (a b : R) (hb : b ≠ 0) :
    Function.Bijective (oppositeKernelScale a b) := by
  constructor
  · intro x y h
    exact quotientScale_injective a b hb (congrArg Subtype.val h)
  · intro x
    obtain ⟨r, hr⟩ := Ideal.Quotient.mk_surjective x.val
    have hx : Ideal.Quotient.mk (Ideal.span {b}) r = 0 := by
      have xp := x.property
      change oppositeReduction a b x.val = 0 at xp
      rw [← hr] at xp
      exact xp
    obtain ⟨y, hy⟩ := Ideal.mem_span_singleton.mp
      (Ideal.Quotient.eq_zero_iff_mem.mp hx)
    refine ⟨Ideal.Quotient.mk _ y, Subtype.ext ?_⟩
    change Ideal.Quotient.mk (Ideal.span {a * b}) (b * y) = x.val
    rw [← hy]
    exact hr

def oppositeKernelEquiv (a b : R) (hb : b ≠ 0) :
    (R ⧸ Ideal.span {a}) ≃+ (oppositeReduction a b).toAddMonoidHom.ker :=
  AddEquiv.ofBijective (oppositeKernelScale a b) (oppositeKernelScale_bijective a b hb)

theorem oppositeReduction_card_ker (a b : R) (hb : b ≠ 0) :
    Nat.card (oppositeReduction a b).toAddMonoidHom.ker = Nat.card (R ⧸ Ideal.span {a}) :=
  (Nat.card_congr (oppositeKernelEquiv a b hb).toEquiv).symm

end
end ArtinMatthews.SIntegerFourier
