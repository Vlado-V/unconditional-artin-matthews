module

public import ArtinMatthews.SpectralEisensteinAmbientResolution
public import ArtinMatthews.SpectralEisensteinGreenMultiplier
public import ArtinMatthews.SpectralAmbientGreenAtomPair
public import ArtinMatthews.SpectralCompactGreenSpectralMoments
public import ArtinMatthews.SpectralEisensteinGreenMoments
public import ArtinMatthews.SpectralModularDensity
public import ArtinMatthews.SpectralStoneAllEnergyAtoms
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

/-! The actual ambient Green operator intertwines with the explicit
Green multiplier under the completed Eisenstein analysis. -/
noncomputable section
open Set MeasureTheory
open scoped InnerProductSpace
namespace ArtinMatthews

local instance greenIntertwining_cuspInner (N : ℕ) [NeZero N] :
    InnerProductSpace ℂ (gamma0AllHeightCuspidalMassSpace N) :=
  Submodule.innerProductSpace (𝕜:=ℂ) (E:=Gamma0RegionL2 N) (gamma0AllHeightCuspidalMassSpace N)

theorem gamma0CompactGreen_power_all_atoms (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℕ) (hn : n≠0) :
    inner ℂ (gamma0SmoothSeedMass N ψ) (((gamma0Green N)^n) (gamma0SmoothSeedMass N ψ))=
      (∫ t in Ioi 0,(gamma0StoneFrequencyDensity N ψ t:ℂ)*gamma0EisensteinGreenWeight t^n)+
      ∑' l : Ici (0:ℝ),(‖gamma0AmbientSpectralAtomVector N (gamma0SmoothSeedMass N ψ) (l:ℝ)‖^2:ℝ) •
        gamma0EnergyGreenWeight (l:ℝ)^n := by
  let Y := gamma0CompactResolventCutoff N ψ
  let F := gamma0SmoothSeedMass N ψ
  let D := gamma0StoneDiscreteEnergies N ψ Y
  let U := gamma0StoneGoodEnergy N ψ Y
  let S : Set (Ici (0:ℝ)) := {l | (l:ℝ)∉U}
  let e : D ≃ S :=
    { toFun := fun l => ⟨⟨l.val,l.property.2⟩,l.property.1⟩
      invFun := fun l => ⟨l.val.val,⟨l.property,l.val.property⟩⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [gamma0CompactGreen_power_spectral_moment N ψ Y n hn]
  congr 1
  let f : Ici (0:ℝ) → ℂ := fun l =>
    (‖gamma0AmbientSpectralAtomVector N F (l:ℝ)‖^2:ℝ) • gamma0EnergyGreenWeight (l:ℝ)^n
  calc
    _ = ∑' l : S,f l.val := e.tsum_eq _
    _ = ∑' l : Ici (0:ℝ),S.indicator f l := tsum_subtype S f
    _ = _ := by
      apply tsum_congr
      intro l
      by_cases hl : l∈S
      · exact indicator_of_mem hl _
      · have hg : (l:ℝ)∈U := by
          by_contra h
          exact hl h
        rw [indicator_of_notMem hl]
        change 0=(‖gamma0AmbientSpectralAtomVector N F (l:ℝ)‖^2:ℝ) • gamma0EnergyGreenWeight (l:ℝ)^n
        rw [gamma0CompactStoneAtom_zero_of_good N ψ Y l l.property hg,norm_zero,zero_pow (by decide),zero_smul]

theorem gamma0EisensteinAnalysis_compact_green_moment (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (n : ℕ) (hn : n≠0) :
    inner ℂ (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ))
      (gamma0EisensteinAnalysis N (((gamma0Green N)^n) (gamma0SmoothSeedMass N ψ)))=
      inner ℂ (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ))
        (((gamma0EisensteinGreenMultiplier N)^n) (gamma0EisensteinAnalysis N (gamma0SmoothSeedMass N ψ))) := by
  have hm := gamma0CompactGreen_power_all_atoms N ψ n hn
  rw [gamma0AmbientGreen_weighted_atom_sum] at hm
  have hp := gamma0AmbientEisenstein_spectral_pairing N (gamma0SmoothSeedMass N ψ)
    (((gamma0Green N)^n) (gamma0SmoothSeedMass N ψ))
  simp only [gamma0EisensteinAnalysis_seed] at hp ⊢
  rw [gamma0EisensteinSeedAnalysis_green_moment]
  linear_combination hm-hp

theorem gamma0EisensteinAnalysis_green_moment (N : ℕ) [NeZero N]
    (u : Gamma0RegionL2 N) (n : ℕ) (hn : n≠0) :
    inner ℂ (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N (((gamma0Green N)^n) u))=
      inner ℂ (gamma0EisensteinAnalysis N u)
        (((gamma0EisensteinGreenMultiplier N)^n) (gamma0EisensteinAnalysis N u)) := by
  apply isClosed_property (p:=fun u : Gamma0RegionL2 N =>
    inner ℂ (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N (((gamma0Green N)^n) u))=
      inner ℂ (gamma0EisensteinAnalysis N u)
        (((gamma0EisensteinGreenMultiplier N)^n) (gamma0EisensteinAnalysis N u)))
      (gamma0SmoothSeedMass_denseRange N)
  · apply isClosed_eq
    · exact (gamma0EisensteinAnalysis N).continuous.inner
        ((gamma0EisensteinAnalysis N).continuous.comp ((gamma0Green N)^n).continuous)
    · exact (gamma0EisensteinAnalysis N).continuous.inner
        (((gamma0EisensteinGreenMultiplier N)^n).continuous.comp (gamma0EisensteinAnalysis N).continuous)
  · intro ψ
    exact gamma0EisensteinAnalysis_compact_green_moment N ψ n hn

theorem spectralSesquilinearPair_eq_of_diagonal {V : Type*} [AddCommGroup V] [Module ℂ V]
    (B D : V → V → ℂ)
    (hBa : ∀ x y z,B x (y+z)=B x y+B x z) (hDa : ∀ x y z,D x (y+z)=D x y+D x z)
    (hBla : ∀ x y z,B (x+y) z=B x z+B y z) (hDla : ∀ x y z,D (x+y) z=D x z+D y z)
    (hBs : ∀ c x y,B x (c • y)=c*B x y) (hDs : ∀ c x y,D x (c • y)=c*D x y)
    (hBls : ∀ c x y,B (c • x) y=(starRingEnd ℂ) c*B x y)
    (hDls : ∀ c x y,D (c • x) y=(starRingEnd ℂ) c*D x y)
    (hd : ∀ x,B x x=D x x) : ∀ x y,B x y=D x y := by
  let F (x y : V) := B x y-D x y
  have ha (x y z : V) : F x (y+z)=F x y+F x z := by
    simp only [F,hBa,hDa]
    ring
  have hla (x y z : V) : F (x+y) z=F x z+F y z := by
    simp only [F,hBla,hDla]
    ring
  have hs (c : ℂ) (x y : V) : F x (c • y)=c*F x y := by simp only [F,hBs,hDs,mul_sub]
  have hls (c : ℂ) (x y : V) : F (c • x) y=(starRingEnd ℂ) c*F x y := by
    simp only [F,hBls,hDls,mul_sub]
  have hz (x : V) : F x x=0 := sub_eq_zero.mpr (hd x)
  intro x y
  have h1 := hz (x+y)
  rw [ha,hla,hla,hz,hz,zero_add,add_zero] at h1
  have h2 := hz (x+Complex.I • y)
  rw [ha,hla x (Complex.I • y) x,hla x (Complex.I • y) (Complex.I • y),
    hls Complex.I y x,hs Complex.I x y,hs Complex.I (Complex.I • y) y,hls Complex.I y y,hz x,hz y] at h2
  simp only [mul_zero,zero_add,add_zero,Complex.conj_I] at h2
  have he : (2*Complex.I)*F x y=0 := by linear_combination h2+Complex.I*h1
  exact sub_eq_zero.mp ((mul_eq_zero.mp he).resolve_left (mul_ne_zero (by norm_num) Complex.I_ne_zero))

theorem gamma0EisensteinAnalysis_green_pair (N : ℕ) [NeZero N]
    (u v : Gamma0RegionL2 N) (n : ℕ) (hn : n≠0) :
    inner ℂ (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N (((gamma0Green N)^n) v))=
      inner ℂ (gamma0EisensteinAnalysis N u)
        (((gamma0EisensteinGreenMultiplier N)^n) (gamma0EisensteinAnalysis N v)) := by
  let B (u v : Gamma0RegionL2 N) :=
    inner ℂ (gamma0EisensteinAnalysis N u) (gamma0EisensteinAnalysis N (((gamma0Green N)^n) v))
  let D (u v : Gamma0RegionL2 N) :=
    inner ℂ (gamma0EisensteinAnalysis N u) (((gamma0EisensteinGreenMultiplier N)^n) (gamma0EisensteinAnalysis N v))
  change B u v=D u v
  apply spectralSesquilinearPair_eq_of_diagonal B D _ _ _ _ _ _ _ _ _ u v
  · intro x y z
    simp only [B,map_add,inner_add_right]
  · intro x y z
    simp only [D,map_add,inner_add_right]
  · intro x y z
    simp only [B,map_add,inner_add_left]
  · intro x y z
    simp only [D,map_add,inner_add_left]
  · intro c x y
    simp only [B,map_smul,inner_smul_right]
  · intro c x y
    simp only [D,map_smul,inner_smul_right]
  · intro c x y
    simp only [B,map_smul,inner_smul_left]
  · intro c x y
    simp only [D,map_smul,inner_smul_left]
  · exact fun x => gamma0EisensteinAnalysis_green_moment N x n hn

theorem gamma0EisensteinAnalysis_green_intertwines (N : ℕ) [NeZero N] (u : Gamma0RegionL2 N) :
    gamma0EisensteinAnalysis N (gamma0Green N u)=
      gamma0EisensteinGreenMultiplier N (gamma0EisensteinAnalysis N u) := by
  let A := gamma0EisensteinAnalysis N
  let G := gamma0Green N
  let M := gamma0EisensteinGreenMultiplier N
  have h1 (x y : Gamma0RegionL2 N) : inner ℂ (A x) (A (G y))=inner ℂ (A x) (M (A y)) := by
    simpa only [pow_one] using gamma0EisensteinAnalysis_green_pair N x y 1 (by decide)
  have h2 : inner ℂ (A u) (A (G (G u)))=inner ℂ (A u) (M (M (A u))) := by
    simpa only [pow_two,mul_apply_eq_comp] using gamma0EisensteinAnalysis_green_moment N u 2 (by decide)
  have hs (x y : Gamma0EisensteinSpectralSpace N) : inner ℂ (M x) y=inner ℂ x (M y) :=
    (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (gamma0EisensteinGreenMultiplier_selfAdjoint N)) x y
  have hcross : inner ℂ (M (A u)) (A (G u))=inner ℂ (M (A u)) (M (A u)) := by
    rw [hs,← h1 u (G u),h2,hs]
  apply sub_eq_zero.mp
  apply (inner_self_eq_zero (𝕜:=ℂ)).mp
  rw [inner_sub_sub_self,h1 (G u) u,hcross,sub_self,zero_sub]
  ring

theorem gamma0EisensteinAnalysis_green_operator (N : ℕ) [NeZero N] :
    (gamma0EisensteinAnalysis N).comp (gamma0Green N)=
      (gamma0EisensteinGreenMultiplier N).comp (gamma0EisensteinAnalysis N) := by
  apply ContinuousLinearMap.ext
  intro u
  exact gamma0EisensteinAnalysis_green_intertwines N u


theorem gamma0EisensteinSynthesis_green_intertwines (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) :
    (gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinGreenMultiplier N v)=
      gamma0Green N ((gamma0EisensteinAnalysis N).adjoint v) := by
  have h := congrArg ContinuousLinearMap.adjoint (gamma0EisensteinAnalysis_green_operator N)
  rw [ContinuousLinearMap.adjoint_comp,ContinuousLinearMap.adjoint_comp,
    (gamma0Green_selfAdjoint N).adjoint_eq,(gamma0EisensteinGreenMultiplier_selfAdjoint N).adjoint_eq] at h
  exact (congrArg (fun T => T v) h).symm

theorem gamma0EisensteinSynthesis_kernel_green_invariant (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : (gamma0EisensteinAnalysis N).adjoint v=0) :
    (gamma0EisensteinAnalysis N).adjoint (gamma0EisensteinGreenMultiplier N v)=0 := by
  rw [gamma0EisensteinSynthesis_green_intertwines,hv,map_zero]

theorem gamma0EisensteinAnalysis_range_green_invariant (N : ℕ) [NeZero N]
    (v : Gamma0EisensteinSpectralSpace N) (hv : v∈(gamma0EisensteinAnalysis N).range) :
    gamma0EisensteinGreenMultiplier N v∈(gamma0EisensteinAnalysis N).range := by
  obtain ⟨u,rfl⟩ := hv
  exact ⟨gamma0Green N u,gamma0EisensteinAnalysis_green_intertwines N u⟩

end ArtinMatthews
