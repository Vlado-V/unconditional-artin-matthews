module

public import ArtinMatthews.SourceKPRetainedAverage
public import ArtinMatthews.SourceKPAdelicRootSupportDecomposition
public import ArtinMatthews.SourceThetaFiniteMellin
public import ArtinMatthews.SourceKPCuspResidualFourierSymmetries
public import ArtinMatthews.SourceKPResidualRetainedNonzero
public import ArtinMatthews.SourceKPRetainedCutoff
public import ArtinMatthews.SourceKPRetainedDiagonalFix
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
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
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

/-! The original retained support supplies a nonzero positive seed.
Every factor of the seed is a literal compact-open principal-unit cutoff. -/
namespace ArtinMatthews

open NumberField IsDedekindDomain Matrix StandardAdelic SourcePhysical SourceReflection QuadraticWeil
open scoped NumberField MatrixGroups AdeleRing SourcePhysical Classical BigOperators

noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)

local notation "Pr" => HeightOneSpectrum (𝓞 K)
local notation "Gf" => SourceKPFiniteAdeleProjective K hζ
local notation "Kf" => sourceKPFiniteLevelSubgroup K hζ
local notation "D" => sourceKPFiniteAdeleProjectiveDiagonalLift K hζ

private theorem diagonal_product_level (S : Finset Pr) (qf : Gf)
    (z : ∀ P : S, (P.val.adicCompletion K)ˣ)
    (hz : ∀ P : S, (∃ w : (P.val.adicCompletion K)ˣ, w^3 = z P) ∧
      qf⁻¹ * D (sourceKPAdeleLocalUnit K P.val (z P)) * qf ∈ Kf)
    (U : Finset S) :
    qf⁻¹ * D (∏ P ∈ U, sourceKPAdeleLocalUnit K P.val (z P)) * qf ∈ Kf := by
  induction U using Finset.induction_on with
  | empty =>
    rw [Finset.prod_empty, sourceKPFiniteAdeleProjectiveDiagonalLift_one, mul_one, inv_mul_cancel]
    exact (Kf).one_mem
  | @insert P U hP ih =>
    obtain ⟨⟨w,hw⟩,hPlevel⟩ := hz P
    let u := sourceKPAdeleLocalUnit K P.val (z P)
    let v := ∏ Q ∈ U, sourceKPAdeleLocalUnit K Q.val (z Q)
    have hu : (sourceKPAdeleLocalUnit K P.val w)^3 = u := by
      rw [show u = sourceKPAdeleLocalUnit K P.val (z P) from rfl,
        ← sourceKPRetainedLocalUnitHom_apply, ← sourceKPRetainedLocalUnitHom_apply,
        ← map_pow, hw]
    have hd : D (u*v) = D u * D v := by
      rw [← hu, sourceKPFiniteAdeleProjectiveDiagonalLift_cube_mul_left]
    rw [Finset.prod_insert hP]
    change qf⁻¹*D (u*v)*qf ∈ Kf
    rw [hd, show qf⁻¹*(D u*D v)*qf = (qf⁻¹*D u*qf)*(qf⁻¹*D v*qf) by group]
    exact (Kf).mul_mem hPlevel ih

theorem sourceKPRetainedPositiveSeed_exists
    (S₀ : Finset Pr) (hS : standardWeilBadPlaces K ⊆ sourceHilbertSet K S₀)
    {T : ℝ} (hT : 2 < T) :
    let S := sourceHilbertSet K S₀
    ∃ (a : GL (Fin 2) 𝔸ᶠ[K]) (R M : S → ℕ)
      (U : ∀ P : S, SourceThetaFiniteCutoff K P.val),
      let q₀ := (sourceKPAdelicRootSupportTuple K hζ 1 a S).2
      let C := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
      C q₀ ≠ 0 ∧
      ∀ z : ∀ P : S, (P.val.adicCompletion K)ˣ,
        sourceKPRetainedSeedCoefficient K hζ S R M (one_le_two.trans hT.le) q₀ z =
          C q₀ * ∏ P : S, (U P).factor (z P) := by
  let S := sourceHilbertSet K S₀
  obtain ⟨a,hne⟩ := sourceKPResidualFourierValue_retained_exists_ne_zero K hζ S₀ hS hT
  let q₀ := (sourceKPAdelicRootSupportTuple K hζ 1 a S).2
  let C := sourceKPCuspResidualFourierValue K hζ 1 (one_le_two.trans hT.le)
  choose M hM hperiod using fun P : S => sourceKPRetained_upper_period K hζ P.val q₀
  choose N hN hdiag using fun P : S => sourceKPRetained_small_diagonal_level K hζ P.val q₀
  let R (P : S) : ℕ := sourceDifferentExponent K P.val + N P + 1
  let n (P : S) : ℤ := (sourceDifferentExponent K P.val:ℤ) - (R P:ℤ)
  have hnN (P : S) : n P ≤ -(N P : ℤ) := by
    dsimp [n,R]
    omega
  have hn (P : S) : n P < 0 := (hnN P).trans_lt (by have := hN P; omega)
  let U (P : S) := sourceKPRetainedCutoff K P.val (n P) (hn P)
  refine ⟨a,R,M,U,hne,?_⟩
  intro z
  rw [sourceKPRetainedSeedCoefficient_eq K hζ S R M (one_le_two.trans hT.le) q₀ hperiod z]
  have hprod : (∏ P : S, (U P).factor (z P)) = ∏ P : S,
      if (z P : P.val.adicCompletion K)-1 ∈ sourceLocalBall K P.val (n P) then 1 else 0 :=
    Finset.prod_congr rfl (fun P _ => sourceKPRetainedCutoff_factor K P.val (n P) (hn P) (z P))
  change C (D (sourceKPRetainedDiagonalUnit K S z)*q₀) *
    (∏ P : S, if (z P : P.val.adicCompletion K)-1 ∈ sourceLocalBall K P.val (n P) then 1 else 0) =
      C q₀ * ∏ P : S, (U P).factor (z P)
  rw [← hprod]
  by_cases hz : ∀ P : S, (z P : P.val.adicCompletion K)-1 ∈ sourceLocalBall K P.val (n P)
  · have hlocal (P : S) : (∃ w : (P.val.adicCompletion K)ˣ, w^3 = z P) ∧
        q₀⁻¹ * D (sourceKPAdeleLocalUnit K P.val (z P)) * q₀ ∈ Kf :=
      hdiag P (z P) ((hz P).trans (WithZero.exp_le_exp.mpr (hnN P)))
    have hlevel : q₀⁻¹*D (sourceKPRetainedDiagonalUnit K S z)*q₀ ∈ Kf :=
      diagonal_product_level K hζ S q₀ z hlocal Finset.univ
    have hfix : C (D (sourceKPRetainedDiagonalUnit K S z)*q₀) = C q₀ := calc
      _ = C (q₀*(q₀⁻¹*D (sourceKPRetainedDiagonalUnit K S z)*q₀)) :=
        congrArg C (by group)
      _ = _ := sourceKPCuspResidualFourierValue_right_level K hζ 1 _ q₀ _ hlevel
    rw [hfix]
  · obtain ⟨P,hP⟩ := not_forall.mp hz
    have hzero : (∏ P : S, (U P).factor (z P)) = 0 := by
      rw [hprod]
      exact Finset.prod_eq_zero (Finset.mem_univ P) (if_neg hP)
    rw [hzero, mul_zero, mul_zero]

end
end ArtinMatthews
