module

public import ArtinMatthews.SpectralAmbientGreenMoments
public import ArtinMatthews.SpectralEisensteinAmbientResolution
public import ArtinMatthews.SpectralStoneAllEnergyAtoms
public import ArtinMatthews.SpectralStoneCuspidalAtoms
public import ArtinMatthews.SpectralStoneNativePairing
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
public import Mathlib.RingTheory.PiTensorProduct
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

/-! The complete atomic part of the ambient scalar spectral measure,
paired with powers of the actual Green operator. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

local instance greenAtom_cuspInner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

theorem gamma0AmbientSpectralAtomVector_green_input (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (l : ℝ) :
    gamma0AmbientSpectralAtomVector N (gamma0Green N u) l=
      gamma0EnergyGreenWeight l • gamma0AmbientSpectralAtomVector N u l := by
  let K := gamma0AmbientEnergyEigenspace N l
  let P := K.starProjection
  have hreal : (starRingEnd ℂ) (gamma0EnergyGreenWeight l)=gamma0EnergyGreenWeight l := by
    rw [gamma0EnergyGreenWeight_eq_real,Complex.conj_ofReal]
  simp only [gamma0AmbientSpectralAtomVector_eq_projection]
  change P (gamma0Green N u)=gamma0EnergyGreenWeight l • P u
  apply ext_inner_left ℂ
  intro w
  have hP := K.inner_starProjection_left_eq_right w (gamma0Green N u)
  have hG := (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gamma0Green_selfAdjoint N)) (P w) u
  have hw : gamma0Green N (P w)=gamma0EnergyGreenWeight l • P w := by
    rw [gamma0EnergyGreenWeight_eq_real]
    exact (mem_gamma0AmbientEnergyEigenspace_iff N l (P w)).mp (K.starProjection_apply_mem w)
  change inner ℂ (P w) (gamma0Green N u)=inner ℂ w (P (gamma0Green N u)) at hP
  change inner ℂ (gamma0Green N (P w)) u=inner ℂ (P w) (gamma0Green N u) at hG
  rw [← hP,← hG,hw,inner_smul_left,hreal,inner_smul_right,K.inner_starProjection_left_eq_right]

theorem gamma0AmbientSpectralAtomVector_green_power_input (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (l : ℝ) (n : ℕ) :
    gamma0AmbientSpectralAtomVector N (((gamma0Green N)^n) u) l=
      gamma0EnergyGreenWeight l^n • gamma0AmbientSpectralAtomVector N u l := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [pow_succ',mul_apply_eq_comp,gamma0AmbientSpectralAtomVector_green_input,ih,pow_succ',mul_smul]

theorem gamma0AmbientAtomPair_summable (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    Summable (fun l : Ici (0:ℝ) => inner ℂ
      (gamma0AmbientSpectralAtomVector N u (l:ℝ)) (gamma0AmbientSpectralAtomVector N v (l:ℝ))) := by
  apply ((gamma0AmbientAtomNormSq_summable N u).add (gamma0AmbientAtomNormSq_summable N v)).of_norm_bounded
  intro l
  refine (norm_inner_le_norm (𝕜:=ℂ) _ _).trans ?_
  nlinarith [sq_nonneg (‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖-
    ‖gamma0AmbientSpectralAtomVector N v (l:ℝ)‖)]

def gamma0AmbientAtomPair (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) : ℂ :=
  ∑' l : Ici (0:ℝ),inner ℂ (gamma0AmbientSpectralAtomVector N u (l:ℝ))
    (gamma0AmbientSpectralAtomVector N v (l:ℝ))

theorem gamma0AmbientAtomPair_add_right (N : ℕ) [NeZero N] (u v w : Gamma0RegionL2 N) :
    gamma0AmbientAtomPair N u (v+w)=gamma0AmbientAtomPair N u v+gamma0AmbientAtomPair N u w := by
  simp only [gamma0AmbientAtomPair,gamma0AmbientSpectralAtomVector_eq_projection,map_add,inner_add_right]
  simpa only [gamma0AmbientSpectralAtomVector_eq_projection] using
    (gamma0AmbientAtomPair_summable N u v).tsum_add (gamma0AmbientAtomPair_summable N u w)

theorem gamma0AmbientAtomPair_smul_right (N : ℕ) [NeZero N] (c : ℂ) (u v : Gamma0RegionL2 N) :
    gamma0AmbientAtomPair N u (c • v)=c*gamma0AmbientAtomPair N u v := by
  simp only [gamma0AmbientAtomPair,gamma0AmbientSpectralAtomVector_eq_projection,map_smul,inner_smul_right]
  exact tsum_mul_left

theorem gamma0AmbientAtomPair_conj (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    (starRingEnd ℂ) (gamma0AmbientAtomPair N u v)=gamma0AmbientAtomPair N v u := by
  have h := Complex.conjCLE.toContinuousLinearMap.map_tsum (gamma0AmbientAtomPair_summable N u v)
  change (starRingEnd ℂ) (gamma0AmbientAtomPair N u v)=
    ∑' l : Ici (0:ℝ),(starRingEnd ℂ) (inner ℂ (gamma0AmbientSpectralAtomVector N u (l:ℝ))
      (gamma0AmbientSpectralAtomVector N v (l:ℝ))) at h
  simp only [inner_conj_symm] at h
  exact h

theorem gamma0AmbientAtomPair_diagonal (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0AmbientAtomPair N u u=
      ((∑' l : Ici (0:ℝ),‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2):ℝ) := by
  have h := Complex.ofRealCLM.map_tsum (gamma0AmbientAtomNormSq_summable N u)
  change (((∑' l : Ici (0:ℝ),‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2):ℝ):ℂ)=
    ∑' l : Ici (0:ℝ),((‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2:ℝ):ℂ) at h
  rw [gamma0AmbientAtomPair,h]
  apply tsum_congr
  intro l
  rw [inner_self_eq_norm_sq_to_K (𝕜:=ℂ),Complex.ofReal_pow]
  rfl

theorem gamma0AmbientAtomPair_native_split (N : ℕ) [NeZero N] (u v : Gamma0RegionL2 N) :
    gamma0AmbientAtomPair N u v=
      inner ℂ (gamma0CuspidalProjection N u) (gamma0CuspidalProjection N v)+
        inner ℂ u (gamma0ResidualProjection N v) := by
  rw [gamma0ResidualProjection_inner]
  let D (u v : Gamma0RegionL2 N) :=
    inner ℂ (gamma0CuspidalProjection N u).val (gamma0CuspidalProjection N v).val+gamma0StoneResidualPair N u v
  change gamma0AmbientAtomPair N u v=D u v
  apply spectralHermitianPair_eq_of_diagonal (gamma0AmbientAtomPair N) D
    (gamma0AmbientAtomPair_add_right N) _ (gamma0AmbientAtomPair_smul_right N) _
    (gamma0AmbientAtomPair_conj N) _ _ u v
  · intro x y z
    simp only [D,map_add,Submodule.coe_add,inner_add_right,gamma0StoneResidualPair_add_right]
    ring
  · intro c x y
    simp only [D,map_smul,Submodule.coe_smul,inner_smul_right,gamma0StoneResidualPair_smul_right,mul_add]
  · intro x y
    simp only [D,map_add,inner_conj_symm,gamma0StoneResidualPair_conj]
  · intro x
    rw [gamma0AmbientAtomPair_diagonal,gamma0AmbientAtomNormSq_sum_split,Complex.ofReal_add]
    change _=inner ℂ (gamma0CuspidalProjection N x).val (gamma0CuspidalProjection N x).val+gamma0StoneResidualPair N x x
    rw [gamma0StoneResidualPair_diagonal,inner_self_eq_norm_sq_to_K (𝕜:=ℂ),Complex.ofReal_pow]
    rfl

theorem gamma0AmbientGreen_weighted_atom_sum (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (n : ℕ) :
    (∑' l : Ici (0:ℝ),(‖gamma0AmbientSpectralAtomVector N u (l:ℝ)‖^2:ℝ) •
      gamma0EnergyGreenWeight (l:ℝ)^n)=
      inner ℂ (gamma0CuspidalProjection N u) (gamma0CuspidalProjection N (((gamma0Green N)^n) u))+
        inner ℂ u (gamma0ResidualProjection N (((gamma0Green N)^n) u)) := by
  rw [← gamma0AmbientAtomPair_native_split,gamma0AmbientAtomPair]
  apply tsum_congr
  intro l
  rw [gamma0AmbientSpectralAtomVector_green_power_input,inner_smul_right,
    inner_self_eq_norm_sq_to_K (𝕜:=ℂ),Complex.real_smul,Complex.ofReal_pow]
  exact mul_comm _ _

end ArtinMatthews
