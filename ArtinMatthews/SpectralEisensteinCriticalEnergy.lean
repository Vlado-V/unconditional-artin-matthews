module

public import ArtinMatthews.SpectralEisensteinUpperCutoffEnergy
public import ArtinMatthews.SpectralEisensteinRegularMatching
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
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

/-! The genuine truncated Eisenstein combination at a regular parameter.
All low-band forcings cancel and only its actual upper cutoff bands remain. -/
noncomputable section
open Set Matrix
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CuspScatteringMatrix (N : ℕ) [NeZero N] (s : ℂ) :
    Matrix (Gamma0EisensteinCuspClasses N) (Gamma0EisensteinCuspClasses N) ℂ :=
  fun j i => gamma0EisensteinMatchedCoefficient N (gamma0EisensteinCuspClassRepresentative N i) s j

def gamma0EisensteinFluxScale (N : ℕ) : ℝ := (4*(N:ℝ))⁻¹

theorem gamma0EisensteinFluxScale_pos (N : ℕ) [NeZero N] : 0<gamma0EisensteinFluxScale N := by
  unfold gamma0EisensteinFluxScale
  exact inv_pos.mpr (mul_pos (by norm_num) (Nat.cast_pos.mpr (NeZero.pos N)))

theorem gamma0EisensteinFluxScale_lt_half (N : ℕ) [NeZero N] : gamma0EisensteinFluxScale N<1/2 := by
  have hN : (1:ℝ)≤N := by exact_mod_cast (NeZero.pos N)
  unfold gamma0EisensteinFluxScale
  rw [← one_div]
  exact (div_lt_iff₀ (by positivity : (0:ℝ)<4*(N:ℝ))).mpr (by linarith)

theorem gamma0EisensteinFluxScale_lower_edge (N : ℕ) : 1/gamma0EisensteinFluxScale N=4*(N:ℝ) := by
  rw [gamma0EisensteinFluxScale,one_div,inv_inv]

theorem gamma0EisensteinFluxScale_raw_low (N : ℕ) [NeZero N] (r : SL(2,ℤ))
    {y : ℝ} (hy : y≤gamma0EisensteinMatchingHeight N) :
    y/(gamma0CuspTrueWidth N r:ℝ)<1/gamma0EisensteinFluxScale N := by
  have hw : (0:ℝ)<gamma0CuspTrueWidth N r := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hw1 : (1:ℝ)≤gamma0CuspTrueWidth N r := by exact_mod_cast (gamma0CuspTrueWidth_pos N r)
  have hN : (0:ℝ)<N := Nat.cast_pos.mpr (NeZero.pos N)
  have hy' : y/(gamma0CuspTrueWidth N r:ℝ)≤gamma0EisensteinMatchingHeight N :=
    (div_le_iff₀ hw).mpr (hy.trans (le_mul_of_one_le_right (gamma0EisensteinMatchingHeight_pos N).le hw1))
  rw [gamma0EisensteinFluxScale_lower_edge]
  exact hy'.trans_lt (by unfold gamma0EisensteinMatchingHeight;linarith)

def gamma0EisensteinCriticalBaseEnergy (N : ℕ) [NeZero N] (s : ℂ)
    (c : Gamma0EisensteinCuspClasses N → ℂ) : gamma0EnergySpace N :=
  ∑ i,c i • gamma0CuspEisensteinMatchedTruncatedEnergy N (gamma0EisensteinCuspClassRepresentative N i) s

def gamma0EisensteinCriticalTruncatedEnergy (N : ℕ) [NeZero N] (s : ℂ)
    (c : Gamma0EisensteinCuspClasses N → ℂ) : gamma0EnergySpace N :=
  let A := gamma0EisensteinFluxScale N
  let hA := gamma0EisensteinFluxScale_pos N
  let r := gamma0EisensteinCuspClassRepresentative N
  let b := (gamma0CuspScatteringMatrix N s).mulVec c
  gamma0EisensteinCriticalBaseEnergy N s c+
    (∑ j,c j • gamma0CuspUpperTruncatedEnergy N (r j) s A hA)+
    (∑ j,b j • gamma0CuspUpperTruncatedEnergy N (r j) (1-s) A hA)

def gamma0EisensteinCriticalTopForcing (N : ℕ) [NeZero N] (s : ℂ)
    (c : Gamma0EisensteinCuspClasses N → ℂ) : Gamma0RegionL2 N :=
  let A := gamma0EisensteinFluxScale N
  let hA := gamma0EisensteinFluxScale_pos N
  let r := gamma0EisensteinCuspClassRepresentative N
  let b := (gamma0CuspScatteringMatrix N s).mulVec c
  (∑ j,c j • gamma0CuspUpperCutoffForcingMass N (r j) s A hA)+
    (∑ j,b j • gamma0CuspUpperCutoffForcingMass N (r j) (1-s) A hA)

theorem spectralSum_smul_matrix_mulVec {ι V : Type*} [Fintype ι] [AddCommMonoid V] [Module ℂ V]
    (A : Matrix ι ι ℂ) (c : ι → ℂ) (v : ι → V) :
    (∑ i,c i • (∑ j,A j i • v j))=∑ j,A.mulVec c j • v j := by
  simp only [Finset.smul_sum,smul_smul,Matrix.mulVec,dotProduct,Finset.sum_smul]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro j _
  apply Finset.sum_congr rfl
  intro i _
  rw [mul_comm (c i)]

theorem gamma0EisensteinCriticalBaseEnergy_pencil (N : ℕ) [NeZero N] (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    let r := gamma0EisensteinCuspClassRepresentative N
    let b := (gamma0CuspScatteringMatrix N s).mulVec c
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0EisensteinCriticalBaseEnergy N s c)=
      gamma0EnergyMassAdjoint N
        (-(∑ j,c j • gamma0CuspEisensteinCompactForcingMass N (r j) s)-
          ∑ j,b j • gamma0CuspEisensteinCompactForcingMass N (r j) (1-s)) := by
  dsimp only
  rw [gamma0EisensteinCriticalBaseEnergy,map_sum]
  simp_rw [map_smul,gamma0CuspEisensteinMatchedTruncatedEnergy_pencil_regular N _ s hs]
  simp_rw [← (gamma0EnergyMassAdjoint N).map_smul]
  rw [← map_sum]
  congr 1
  simp only [gamma0EisensteinMatchedForcing,smul_sub,smul_neg,Finset.sum_sub_distrib,Finset.sum_neg_distrib]
  exact congrArg (fun u : Gamma0RegionL2 N =>
    -(∑ j,c j • gamma0CuspEisensteinCompactForcingMass N (gamma0EisensteinCuspClassRepresentative N j) s)-u)
    (spectralSum_smul_matrix_mulVec (gamma0CuspScatteringMatrix N s) c
      (fun j => gamma0CuspEisensteinCompactForcingMass N (gamma0EisensteinCuspClassRepresentative N j) (1-s)))

theorem gamma0CuspUpperTruncatedEnergy_sum_pencil (N : ℕ) [NeZero N] (q : ℂ) (A : ℝ)
    (hA : 0<A) (hA2 : A≤1/2) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    let r := gamma0EisensteinCuspClassRepresentative N
    gamma0EnergyResolventPencil N (q*(1-q))
      (∑ j,c j • gamma0CuspUpperTruncatedEnergy N (r j) q A hA)=
        gamma0EnergyMassAdjoint N
          ((∑ j,c j • gamma0CuspEisensteinCompactForcingMass N (r j) q)-
            ∑ j,c j • gamma0CuspUpperCutoffForcingMass N (r j) q A hA) := by
  dsimp only
  rw [map_sum]
  simp_rw [map_smul,gamma0CuspUpperTruncatedEnergy_pencil N _ q A hA hA2]
  simp_rw [← (gamma0EnergyMassAdjoint N).map_smul]
  rw [← map_sum]
  congr 1
  simp only [smul_sub,Finset.sum_sub_distrib]

theorem gamma0EisensteinCriticalTruncatedEnergy_pencil (N : ℕ) [NeZero N] (s : ℂ)
    (hs : gamma0EisensteinMatchingRegular N s) (c : Gamma0EisensteinCuspClasses N → ℂ) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0EisensteinCriticalTruncatedEnergy N s c)=
      gamma0EnergyMassAdjoint N (-gamma0EisensteinCriticalTopForcing N s c) := by
  let A := gamma0EisensteinFluxScale N
  let hA := gamma0EisensteinFluxScale_pos N
  have hA2 := (gamma0EisensteinFluxScale_lt_half N).le
  have hi := gamma0CuspUpperTruncatedEnergy_sum_pencil N s A hA hA2 c
  have ho := gamma0CuspUpperTruncatedEnergy_sum_pencil N (1-s) A hA hA2
    ((gamma0CuspScatteringMatrix N s).mulVec c)
  dsimp only at hi ho
  rw [gamma0Eisenstein_reflect_parameter] at ho
  rw [gamma0EisensteinCriticalTruncatedEnergy,map_add,map_add,
    gamma0EisensteinCriticalBaseEnergy_pencil N s hs c,hi,ho,← map_add,← map_add]
  congr 1
  unfold gamma0EisensteinCriticalTopForcing
  dsimp only [A,hA]
  rw [neg_add_rev]
  abel

end ArtinMatthews
