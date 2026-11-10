module

public import ArtinMatthews.MarkedMinorArcSharedCoordinates
public import ArtinMatthews.MarkedMinorArcCellGeometry
public import ArtinMatthews.MarkedMinorArcShearOperator
public import ArtinMatthews.MarkedMinorArcCompression
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual position-cell clean kernel, before choosing shared-lattice or
reduced coordinates. Prime-line conditions and source cells are retained. -/
namespace ArtinMatthews
open Matrix MeasureTheory
open scoped BigOperators Matrix.Norms.L2Operator

local instance : Fact (0 < (1 : ℝ)) := ⟨by norm_num⟩

/-- The literal position kernel with its actual determinant divided by the
shared squarefree label product D. -/
noncomputable def markedMinorPositionCleanProductMatrix (ψ : SchwartzMap ℝ ℂ)
    (D : ℕ) (Y Q : ℝ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ) : Matrix (P × S) (P × S) ℂ :=
  fun pb qa => ((Y : ℂ)⁻¹)*ψ (((markedMinorIntegerDet pb.1.1 qa.1.1/(D : ℤ) : ℤ) : ℝ)/Y) *
    ∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
      fourier (markedMinorIntegerDet pb.1.1 qa.1.1/(D : ℤ)-pb.2.1+qa.2.1) θ ∂AddCircle.haarAddCircle

/-- The actual first-good-root test gives exactly the shear required by the
position-cell geometry, using the source complement ratio tau(w)/tau(z). -/
theorem markedMinorPosition_shearGood_of_firstGood {ι : Type*} [Fintype ι]
    (D : ι → ℕ) (i : ι) (r Y : ℝ) (z w : ℤ × ℤ)
    (hg : ((markedMinorIntegerTau r w/markedMinorIntegerTau r z : ℝ) : AddCircle (1:ℝ)) ∉
      markedFirstBadRoots D ⌊Y^(1/5 : ℝ)⌋₊ (Y^(-7/10 : ℝ))) :
    MarkedMinorShearGood ((D i : ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z) Y := by
  apply markedMinorShearGood_of_firstGood D i _ _ hg
  rw [mul_div_assoc,← nsmul_eq_mul,AddCircle.coe_nsmul]

/-- The actual original-position operator equals a principal restriction of
the sheared operator under canonical shared coordinates. -/
theorem markedMinorPositionCleanProductMatrix_submatrix (ψ : SchwartzMap ℝ ℂ)
    {D : ℕ} (hD : D ≠ 0) (Y Q : ℝ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ)
    (z w : ℤ × ℤ) (hd : markedMinorIntegerDet z w=1)
    (hdiv : ∀ v ∈ P, (D : ℤ) ∣ markedMinorIntegerDet z v) :
    ∃ e : (P × S) → ((P.image (markedMinorSharedCoordinates D z w)) × S),
      Function.Injective e ∧ markedMinorPositionCleanProductMatrix ψ D Y Q P S =
        (markedMinorShearCleanProductMatrix ψ Y Q
          (P.image (markedMinorSharedCoordinates D z w)) S).submatrix e e := by
  classical
  let e : (P × S) → ((P.image (markedMinorSharedCoordinates D z w)) × S) :=
    fun pb => (⟨markedMinorSharedCoordinates D z w pb.1.1,
      Finset.mem_image.mpr ⟨pb.1.1,pb.1.2,rfl⟩⟩,pb.2)
  refine ⟨e,?_,?_⟩
  · intro pb qa he
    have h₁ := congrArg (fun t => t.1.1) he
    have h₂ := congrArg Prod.snd he
    have hpos := markedMinorSharedCoordinates_inj hD z w pb.1.1 qa.1.1 hd
      (hdiv _ pb.1.2) (hdiv _ qa.1.2) h₁
    exact Prod.ext (Subtype.ext hpos) h₂
  · ext pb qa
    have hdet := markedMinorSharedCoordinates_determinant hD z w pb.1.1 qa.1.1 hd
      (hdiv _ pb.1.2) (hdiv _ qa.1.2)
    unfold markedMinorPositionCleanProductMatrix markedMinorShearCleanProductMatrix Matrix.submatrix
    change ((Y : ℂ)⁻¹)*ψ (((markedMinorIntegerDet pb.1.1 qa.1.1/(D : ℤ) : ℤ) : ℝ)/Y) *
        (∫ θ : AddCircle (1:ℝ) in (markedMinorCircleMajor Q Y)ᶜ,
          fourier (markedMinorIntegerDet pb.1.1 qa.1.1/(D : ℤ)-pb.2.1+qa.2.1) θ ∂AddCircle.haarAddCircle) = _
    rw [hdet]
    rfl

set_option maxHeartbeats 1000000 in
/-- Actual position-cell minor kernel decay. All same-line and cell hypotheses
are literal source geometry; no shared-lattice support or operator bound is
assumed. The major-arc exponent is independent of the marking bands. -/
theorem marked_minor_position_clean_product_opNorm (ψ : SchwartzMap ℝ ℂ)
    {G H c B R : ℝ} (hG : 0 < G) (hH : 1 ≤ H) (hc : 0 < c) (hB : 0 ≤ B) (hR : 0 ≤ R) :
    ∀ᶠ Λ : ℝ in Filter.atTop, ∀ (Y r : ℝ) (D : ℕ) (P : Finset (ℤ × ℤ)) (S : Finset ℤ)
      (z w : ℤ × ℤ),
      Real.exp (Λ^(1/10 : ℝ)) ≤ Y → Y ≤ Real.exp (H*Λ^(1/5 : ℝ)) →
      0 < D → Squarefree D → markedMinorIntegerDet z w=1 →
      MarkedMinorShearGood ((D : ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z) Y →
      c ≤ |markedMinorIntegerTau r z| → |markedMinorIntegerTau r z| ≤ B →
      (∀ v ∈ P, c ≤ |markedMinorIntegerTau r v| ∧ |markedMinorIntegerTau r v| ≤ B) →
      (∀ v ∈ P, ∀ p ∈ D.primeFactors, MarkedMinorSamePrimeLine p z v) →
      (∀ v ∈ P, |(v.2 : ℝ)/markedMinorIntegerTau r v-(z.2 : ℝ)/markedMinorIntegerTau r z| ≤ R*D*Y) →
      ‖markedMinorPositionCleanProductMatrix ψ D Y (Λ^(G+3)) P S‖ ≤ Λ^(-G) := by
  classical
  let C := max 1 (max (B/c) (R*B^2))
  have hC : 1 ≤ C := le_max_left _ _
  have hC₁ : B/c ≤ C := (le_max_left _ _).trans (le_max_right _ _)
  have hC₂ : R*B^2 ≤ C := (le_max_right _ _).trans (le_max_right _ _)
  filter_upwards [marked_minor_shear_clean_product_opNorm ψ hG hC hH] with Λ hΛ
  intro Y r D P S z w hYlo hYhi hD hDsq hd hg hzlo hzhi hτ hlines hcell
  have hYp : 0 < Y := (Real.exp_pos _).trans_le hYlo
  have hdiv : ∀ v ∈ P, (D : ℤ) ∣ markedMinorIntegerDet z v :=
    fun v hv => markedMinorSamePrimeLines_dvd hDsq z v (hlines v hv)
  have hpoints : ∀ p ∈ P.image (markedMinorSharedCoordinates D z w),
      |(p.1 : ℝ)+(p.2 : ℝ)*((D : ℝ)*markedMinorIntegerTau r w/markedMinorIntegerTau r z)| ≤ C ∧
      |(p.2 : ℝ)/Y| ≤ C := by
    intro p hp
    obtain ⟨v,hv,rfl⟩ := Finset.mem_image.mp hp
    have hrep := markedMinorSharedCoordinates_decompose hD.ne' z w v hd (hdiv v hv)
    have hb := markedMinorSharedLattice_cell_bounds r hYp hc hB hR D hD z w v hd
      (markedMinorSharedCoordinates D z w v).1 (markedMinorSharedCoordinates D z w v).2
      hrep.1 hrep.2 hzlo hzhi (hτ v hv).1 (hτ v hv).2 (hcell v hv)
    exact ⟨hb.1.trans hC₁,hb.2.trans hC₂⟩
  obtain ⟨e,he,heq⟩ := markedMinorPositionCleanProductMatrix_submatrix ψ hD.ne' Y (Λ^(G+3)) P S z w hd hdiv
  rw [heq]
  exact (markedMinorSubmatrix_injective_norm_le _ e he).trans
    (hΛ Y _ _ S hYlo hYhi hg hpoints)

end ArtinMatthews
