module

public import ArtinMatthews.SpectralGamma0EllipticNativePair
public import ArtinMatthews.SpectralGamma0EllipticCoreEnergy
public import ArtinMatthews.SpectralGamma0EnergyDense
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
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

/-! The actual Γ₀ energy completion maps into the native strong closure of
compact smooth Euclidean gradients.  H1Zero membership is proved from the
actual dense smooth core; it is not an input to the regularity adapter. -/

noncomputable section
open Set MeasureTheory
open scoped MatrixGroups ContDiff
open OAI.Analysis.PDE.Weak OAI.Analysis.PDE.Variational

namespace ArtinMatthews

theorem exists_real_bounded_extension_of_dense_functions {D E F : Type*}
    [AddCommGroup D] [Module ℝ D]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    (f : D → F) (e : D → E) (he : DenseRange e)
    (hfadd : ∀ x y, f (x+y) = f x+f y) (hfsmul : ∀ (c : ℝ) x, f (c • x) = c • f x)
    (headd : ∀ x y, e (x+y) = e x+e y) (hesmul : ∀ (c : ℝ) x, e (c • x) = c • e x)
    (hb : ∃ C : ℝ, ∀ d, ‖f d‖ ≤ C * ‖e d‖) :
    ∃ A : E →L[ℝ] F, ∀ d, A (e d) = f d := by
  let fl : D →ₗ[ℝ] F := { toFun := f, map_add' := hfadd, map_smul' := hfsmul }
  let el : D →ₗ[ℝ] E := { toFun := e, map_add' := headd, map_smul' := hesmul }
  exact ⟨fl.extendOfNorm el,LinearMap.extendOfNorm_eq he hb⟩

variable (φ : SchwartzMap (ℝ × ℝ) ℂ) {A a b : ℝ}
  (ha : 0 < a) (hφ : tsupport φ ⊆ spectralPlaneRectangle A a b)
  (r : SL(2, ℤ)) (L : ℂ →L[ℝ] ℝ)

def gamma0EllipticSeedPair (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) : H1Pair 1 :=
  spectralEllipticSmoothPair L (gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ)
    (gamma0EllipticLocalizedSchwartz_compact φ ha hφ r N ψ)

theorem gamma0EllipticSeedPair_add (N : ℕ) [NeZero N] (ψ ξ : h2SmoothCompactSeeds) :
    gamma0EllipticSeedPair φ ha hφ r L N (ψ+ξ) =
      gamma0EllipticSeedPair φ ha hφ r L N ψ + gamma0EllipticSeedPair φ ha hφ r L N ξ := by
  unfold gamma0EllipticSeedPair
  simp only [gamma0EllipticLocalizedSchwartz_add]
  exact spectralEllipticSmoothPair_add L _ _ _ _

theorem gamma0EllipticSeedPair_smul (N : ℕ) [NeZero N] (c : ℝ) (ψ : h2SmoothCompactSeeds) :
    gamma0EllipticSeedPair φ ha hφ r L N (c • ψ) = c • gamma0EllipticSeedPair φ ha hφ r L N ψ := by
  unfold gamma0EllipticSeedPair
  simp only [gamma0EllipticLocalizedSchwartz_smul]
  exact spectralEllipticSmoothPair_smul L c _ _

def gamma0EllipticSeedPairLinear (N : ℕ) [NeZero N] : h2SmoothCompactSeeds →ₗ[ℝ] H1Pair 1 where
  toFun := gamma0EllipticSeedPair φ ha hφ r L N
  map_add' := gamma0EllipticSeedPair_add φ ha hφ r L N
  map_smul' := gamma0EllipticSeedPair_smul φ ha hφ r L N

theorem gamma0EllipticSeedPair_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds),
      ‖gamma0EllipticSeedPair φ ha hφ r L N ψ‖ ≤ C*‖gamma0EnergyTest N ψ‖ := by
  obtain ⟨C,hC,hbound⟩ := gamma0EllipticLocalizedScalar_energy_bound φ ha hφ r L
  refine ⟨Real.sqrt C,Real.sqrt_pos.mpr hC,fun N _ ψ => ?_⟩
  apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _))).mp
  rw [mul_pow,Real.sq_sqrt hC.le]
  exact (spectralEllipticSmoothPair_norm_sq_le_energy L _ _).trans (hbound N ψ)

private theorem gamma0EllipticSeedPair_linear_bound (N : ℕ) [NeZero N] :
    ∃ C : ℝ, ∀ ψ : h2SmoothCompactSeeds,
      ‖gamma0EllipticSeedPairLinear φ ha hφ r L N ψ‖ ≤
        C*‖(gamma0EnergyTestLinear N).restrictScalars ℝ ψ‖ := by
  obtain ⟨C,_,hC⟩ := gamma0EllipticSeedPair_bound φ ha hφ r L
  exact ⟨C,hC N⟩

private theorem gamma0EllipticPair_exists (N : ℕ) [NeZero N] :
    ∃ P : gamma0EnergySpace N →L[ℝ] H1Pair 1,
      ∀ ψ, P (gamma0EnergyTest N ψ) = gamma0EllipticSeedPair φ ha hφ r L N ψ := by
  obtain ⟨C,_,hC⟩ := gamma0EllipticSeedPair_bound φ ha hφ r L
  exact exists_real_bounded_extension_of_dense_functions
    (gamma0EllipticSeedPair φ ha hφ r L N) (gamma0EnergyTest N) (gamma0EnergyTest_dense N)
    (gamma0EllipticSeedPair_add φ ha hφ r L N) (gamma0EllipticSeedPair_smul φ ha hφ r L N)
    (gamma0EnergyTestLinear N).map_add ((gamma0EnergyTestLinear N).restrictScalars ℝ).map_smul
    ⟨C,hC N⟩

def gamma0EllipticPair (N : ℕ) [NeZero N] : gamma0EnergySpace N →L[ℝ] H1Pair 1 :=
  (gamma0EllipticPair_exists φ ha hφ r L N).choose

theorem gamma0EllipticPair_apply (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    gamma0EllipticPair φ ha hφ r L N (gamma0EnergyTest N ψ) =
      gamma0EllipticSeedPair φ ha hφ r L N ψ :=
  (gamma0EllipticPair_exists φ ha hφ r L N).choose_spec ψ

theorem gamma0EllipticPair_mem_H1Zero (N : ℕ) [NeZero N] (u : gamma0EnergySpace N) :
    gamma0EllipticPair φ ha hφ r L N u ∈ H1Zero (univ : Set (Fin 2 → ℝ)) := by
  apply isClosed_property (gamma0EnergyTest_dense N)
    (isClosed_closure.preimage (gamma0EllipticPair φ ha hφ r L N).continuous)
  intro ψ
  change gamma0EllipticPair φ ha hφ r L N (gamma0EnergyTest N ψ) ∈ _
  rw [gamma0EllipticPair_apply]
  exact spectralEllipticSmoothPair_mem_H1Zero L _ _

theorem gamma0EllipticPair_seed_value_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    (gamma0EllipticPair φ ha hφ r L N (gamma0EnergyTest N ψ)).1 =ᵐ[volume]
      fun x : Fin 2 → ℝ => L (φ (spectralEllipticCoordinates x) *
        gamma0CuspSection N ψ r (UpperHalfPlane.ofComplex
          (Complex.equivRealProdCLM.symm (spectralEllipticCoordinates x)))) := by
  rw [gamma0EllipticPair_apply]
  apply (spectralEllipticSmoothPair_value_ae L _ _).trans
  exact Filter.Eventually.of_forall (fun x => by
    simp only [spectralEllipticScalar,gamma0EllipticLocalizedSchwartz_apply]
    simp only [Complex.equivRealProdCLM_symm_apply])

theorem gamma0EllipticPair_seed_gradient_ae (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds) :
    (gamma0EllipticPair φ ha hφ r L N (gamma0EnergyTest N ψ)).2 =ᵐ[volume]
      fun x => WithLp.toLp 2 (fun i : Fin 2 =>
        L (fderiv ℝ (gamma0EllipticLocalizedSchwartz φ ha hφ r N ψ)
          (spectralEllipticCoordinates x) (spectralPlaneDirection i))) := by
  rw [gamma0EllipticPair_apply]
  exact spectralEllipticSmoothPair_gradient_ae L _ _

end ArtinMatthews
