module

public import ArtinMatthews.SourceKPJacquetDeepSmooth
public import ArtinMatthews.SourceKPAdelicCoordinateJacquetPeriod
public import ArtinMatthews.SourceKPJacquetBallCancellation
public import ArtinMatthews.SourceKPJacquetDeepConjugates
public import ArtinMatthews.SourceKPProjectiveBruhatCells
public import ArtinMatthews.SourceKPProjectiveCanonicalFactors
public import ArtinMatthews.SourceKPRetainedCloseCube
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
public import Mathlib.Topology.Algebra.IsOpenUnits
public import Mathlib.Topology.Sheaves.Init


set_option backward.privateInPublic true
@[expose] public section

/-! Actual multiplicative local constancy of the right-diagonal profile
on the finite-conjugate deep-fixed carrier. -/
namespace ArtinMatthews
open NumberField IsDedekindDomain Matrix Matrix.GeneralLinearGroup Filter Topology SourcePhysical
open scoped NumberField MatrixGroups SourcePhysical
noncomputable section

variable (K : Type) [Field K] [NumberField K] {ζ : K} (hζ : IsPrimitiveRoot ζ 12)
    (P : HeightOneSpectrum (𝓞 K))
local notation "L" => P.adicCompletion K
local notation "G" => SourceFiniteKP2Projective K hζ P
local notation "B₀" => SourceFiniteKPProjectiveBorel K hζ P
local notation "J" => sourceKPLocalCompactDeepCoverLevel K hζ P
local notation "D" => sourceKPLocalCompactDeepBase K P
local notation "p₀" => sourceFiniteKP2ProjectiveProjection K hζ P
local notation "l₀" => sourceFiniteKP2ProjectiveLift K hζ P
local notation "a₀" => fun u : Lˣ => l₀ (sourceGL2Diagonal u)
local notation "z₀" => sourceFiniteKP2ProjectiveCenter K hζ P
local notation "B" => sourceLocalBall K P

attribute [local instance] sourceKPLocalProjectiveTopology

local instance sourceKPJacquetDiagonalLocallyConstant_projectiveGroup : IsTopologicalGroup (PGL(2, L)) :=
  inferInstanceAs (IsTopologicalGroup (GL (Fin 2) L ⧸ Subgroup.center (GL (Fin 2) L)))

private theorem sourceKPJacquet_diagonalMatrix_continuous :
    Continuous (sourceGL2DiagonalHom L) := by
  let f := sourceGL2DiagonalHom L
  have hv : Continuous (fun u : Lˣ => (f u : Matrix (Fin 2) (Fin 2) L)) := by
    apply continuous_matrix
    intro i j
    fin_cases i <;> fin_cases j
    · exact Units.continuous_val
    · exact continuous_const
    · exact continuous_const
    · exact continuous_const
  apply Units.continuous_iff.mpr
  refine ⟨hv, ?_⟩
  have he : (fun u : Lˣ => (((f u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L)) =
      (fun u : Lˣ => (f u : Matrix (Fin 2) (Fin 2) L)) ∘ Inv.inv := by
    funext u
    exact congrArg Units.val (f.map_inv u).symm
  change Continuous (fun u : Lˣ => (((f u)⁻¹ : GL (Fin 2) L) : Matrix (Fin 2) (Fin 2) L))
  rw [he]
  exact hv.comp continuous_inv

theorem sourceKPJacquet_diagonal_lift_pow (u : Lˣ) (n : ℕ) : (a₀ u) ^ n = a₀ (u ^ n) := by
  induction n with
  | zero =>
    change (l₀ (sourceGL2Diagonal u)) ^ (0 : ℕ) = l₀ (sourceGL2Diagonal (u ^ (0 : ℕ)))
    rw [pow_zero, pow_zero, show sourceGL2Diagonal (1 : Lˣ) = 1 from (sourceGL2DiagonalHom L).map_one,
      sourceFiniteKP2ProjectiveLift_one]
  | succ n ih =>
    rw [pow_succ, ih]
    change l₀ (sourceGL2Diagonal (u ^ n)) * l₀ (sourceGL2Diagonal u) =
      l₀ (sourceGL2Diagonal (u ^ (n + 1)))
    rw [sourceFiniteKP2ProjectiveLift_diagonal_mul, (sourceFiniteKPHilbert K hζ P).map_pow,
      MonoidHom.pow_apply, sourceFiniteKPHilbert_diag, one_pow, one_pow, map_one, one_mul, pow_succ]

theorem sourceKPJacquet_diagonal_lift_eventually_deep (g : G) :
    ∀ᶠ t : Lˣ in 𝓝 1, (∃ w : Lˣ, w ^ 3 = t) ∧ g⁻¹ * a₀ t * g ∈ J := by
  let q (u : Lˣ) : PGL(2, L) := (p₀ g)⁻¹ * ProjGenLinGroup.mk (sourceGL2Diagonal u) * p₀ g
  have hc : Continuous q :=
    (continuous_const.mul ((sourceKPLocalProjective_mk_continuous K P).comp
      (sourceKPJacquet_diagonalMatrix_continuous K P))).mul continuous_const
  let U := q ⁻¹' (D : Set PGL(2, L))
  have hU : IsOpen U := (sourceKPLocalCompactDeepBase_isOpen K P).preimage hc
  have hU1 : (1 : Lˣ) ∈ U := by
    change (p₀ g)⁻¹ * ProjGenLinGroup.mk (sourceGL2Diagonal (1 : Lˣ)) * p₀ g ∈ D
    rw [show sourceGL2Diagonal (1 : Lˣ) = 1 from (sourceGL2DiagonalHom L).map_one,
      map_one, mul_one, inv_mul_cancel]
    exact (D).one_mem
  let W := (fun x : L => 1 + x) ⁻¹' (Units.val '' U)
  have hW : IsOpen W := ((IsOpenUnits.isOpenEmbedding_unitsVal (M := L)).isOpenMap U hU).preimage
    (continuous_const.add continuous_id)
  have hW0 : (0 : L) ∈ W := ⟨1, hU1, by simp⟩
  obtain ⟨n, hn⟩ := sourceLocalBall_subset_of_mem_nhds_zero K P (hW.mem_nhds hW0)
  obtain ⟨M, _, hCube⟩ := sourceKPRetained_close_cube K P (min n (-1)) (by omega)
  let U₁ := (fun t : Lˣ => (t : L) - 1) ⁻¹' B (-(M : ℤ))
  have hU₁ : IsOpen U₁ := (sourceLocalBall_isOpen K P _).preimage (Units.continuous_val.sub continuous_const)
  have hU₁1 : (1 : Lˣ) ∈ U₁ := by
    change sourceLocalValuation K P ((1 : L) - 1) ≤ WithZero.exp (-(M : ℤ))
    rw [sub_self, map_zero]
    exact zero_le
  filter_upwards [hU₁.mem_nhds hU₁1] with t ht
  obtain ⟨w, hw, hwball⟩ := hCube t ht
  have hwW : ((w : L) - 1) ∈ W := hn (sourceKPJacquetSelfDual_ball_mono K P (min_le_left _ _) hwball)
  obtain ⟨v, hv, he⟩ := hwW
  have hev : v = w := Units.ext (by
    change (v : L) = 1 + ((w : L) - 1) at he
    exact he.trans (by ring))
  have hp : p₀ (g⁻¹ * a₀ w * g) ∈ D := by
    rw [map_mul, map_mul, map_inv]
    exact hev ▸ hv
  have hpow := sourceKPJacquet_deepCover_cube_mem K hζ P hp
  have hcubed := map_pow (MulAut.conj g⁻¹) (a₀ w) (3 : ℕ)
  have hEq : (g⁻¹ * a₀ w * g) ^ (3 : ℕ) = g⁻¹ * a₀ t * g := by
    simpa only [MulAut.conj_apply, inv_inv, sourceKPJacquet_diagonal_lift_pow K hζ P, hw] using hcubed.symm
  exact ⟨⟨w, hw⟩, hEq ▸ hpow⟩

variable {V : Type*} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (SourceFiniteKPProjectiveBorel K hζ P) V)
    (C : Submodule ℂ (sourceAlgebraicInducedSpace _ ρ))
    (hC : ∀ (g : SourceFiniteKP2Projective K hζ P) (f : sourceAlgebraicInducedSpace _ ρ),
      f ∈ C → sourceAlgebraicInducedRepresentation (SourceFiniteKPProjectiveBorel K hζ P) ρ g f ∈ C)
local notation "r₀" => sourceKPJacquetRight K hζ P ρ C hC

theorem sourceKPJacquet_right_diagonal_eventually_eq (f : C)
    (hDeep : SourceKPJacquetDeepFixed K hζ P ρ f.val) (z : Lˣ) :
    ∀ᶠ u : Lˣ in 𝓝 z, r₀ (a₀ u) f = r₀ (a₀ z) f := by
  obtain ⟨F, hF⟩ := hDeep
  have hc : ∀ᶠ t : Lˣ in 𝓝 1, ∃ w : Lˣ, w ^ 3 = t :=
    (sourceKPJacquet_diagonal_lift_eventually_deep K hζ P (1 : G)).mono fun _ h => h.1
  have hJ : ∀ᶠ t : Lˣ in 𝓝 1, ∀ a : ↥F, a.val⁻¹ * a₀ t * a.val ∈ J :=
    Filter.eventually_all.mpr fun a =>
      (sourceKPJacquet_diagonal_lift_eventually_deep K hζ P a.val).mono fun _ h => h.2
  have hRatio : Tendsto (fun u : Lˣ => z⁻¹ * u) (𝓝 z) (𝓝 1) := by
    have hcont : Continuous (fun u : Lˣ => z⁻¹ * u) := continuous_const.mul continuous_id
    simpa only [inv_mul_cancel] using hcont.tendsto z
  filter_upwards [hRatio.eventually (hc.and hJ)] with u ⟨⟨w, hw⟩, hu⟩
  have hD : a₀ z * a₀ (z⁻¹ * u) = a₀ u := by
    change l₀ (sourceGL2Diagonal z) * l₀ (sourceGL2Diagonal (z⁻¹ * u)) = l₀ (sourceGL2Diagonal u)
    rw [sourceFiniteKP2ProjectiveLift_diagonal_mul, ← hw, sourceFiniteKPHilbert_cube_right K hζ P,
      one_pow, map_one, one_mul, hw, mul_inv_cancel_left]
  apply Subtype.ext
  apply Subtype.ext
  funext g
  change f.val.val (g * a₀ u) = f.val.val (g * a₀ z)
  rw [← hD, ← mul_assoc]
  exact hF _ (fun a ha => hu ⟨a, ha⟩) _

theorem sourceKPJacquet_right_diagonal_profile_continuous (f : C)
    (hDeep : SourceKPJacquetDeepFixed K hζ P ρ f.val) (F : C → ℂ) :
    Continuous (fun z : Lˣ => F (r₀ (a₀ z) f)) := by
  apply continuous_iff_continuousAt.mpr
  intro z
  apply continuousAt_const.congr_of_eventuallyEq
  exact (sourceKPJacquet_right_diagonal_eventually_eq K hζ P ρ C hC f hDeep z).mono
    fun _ h => congrArg F h

end
end ArtinMatthews
