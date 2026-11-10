module

public import ArtinMatthews.SpectralCompactResolventCuspSupport
public import ArtinMatthews.SpectralCuspConstantTermGlobal
public import ArtinMatthews.SpectralEisensteinContinuation
public import ArtinMatthews.SpectralCompactResolventWeakMode
public import ArtinMatthews.SpectralCuspComplexEulerEnergy
public import ArtinMatthews.SpectralCuspComplexEulerSolutions
public import ArtinMatthews.SpectralCuspConstantTermEnergy
public import ArtinMatthews.SpectralCuspRayWeakEuler
public import ArtinMatthews.SpectralEisensteinMatchingDefects
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
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
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

/-! The actual full resolvent of any compact forcing has only its
weighted-L² outgoing Euler modes above the genuine cutoff. -/
noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups
namespace ArtinMatthews

def gamma0CompactForcingResolventEnergy (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) : gamma0EnergySpace N :=
  gamma0AmbientWeakResolvent N (s*(1-s)) hs.2 (gamma0SmoothSeedMass N ψ)

theorem gamma0CompactForcingResolventEnergy_pencil (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EnergyResolventPencil N (s*(1-s)) (gamma0CompactForcingResolventEnergy N ψ s hs)=
      gamma0EnergyMassAdjoint N (gamma0SmoothSeedMass N ψ) :=
  gamma0AmbientWeakResolvent_pencil N (s*(1-s)) hs.2 _

theorem gamma0CompactForcingResolventEnergy_mass (N : ℕ) [NeZero N] (ψ : h2SmoothCompactSeeds)
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    gamma0EnergyInclusion N (gamma0CompactForcingResolventEnergy N ψ s hs)=
      gamma0AmbientResolventFamily N (s*(1-s)) (gamma0SmoothSeedMass N ψ) := by
  rw [gamma0AmbientResolventFamily_eq N (s*(1-s)) hs.2]
  rfl

theorem gamma0EnergyMass_outgoing_global_mode_of_pencil (N : ℕ) [NeZero N]
    (r : SL(2,ℤ)) (s : ℂ) (hs : (1/2:ℝ)<s.re)
    (u : gamma0EnergySpace N) (F : Gamma0RegionL2 N)
    (hu : gamma0EnergyResolventPencil N (s*(1-s)) u=gamma0EnergyMassAdjoint N F)
    (Y : ℝ) (hY : 0<Y)
    (hF : ∀ ψ : h2SmoothCompactSeeds,
      (∀ p∈Function.support (fun p : UpperHalfPlane => ψ.val p),Y<p.im) →
      inner ℂ (gamma0SmoothSeedMass N (modularTranslateSmoothSeed r ψ)) F=0) :
    ∃ B : ℂ, gamma0GlobalCuspConstantTerm N r (gamma0EnergyInclusion N u)
      =ᵐ[volume.restrict (Ioi Y)] fun y => B*(y:ℂ)^(1-s) := by
  let U := gamma0EnergyInclusion N u
  let c := gamma0GlobalCuspConstantTerm N r U
  let g := gamma0GlobalCuspConstantTermDerivative N r u
  have hsub : Ioi Y⊆Ioi (0:ℝ) := fun _ hy => hY.trans hy
  obtain ⟨C,G,_,_,hcC,_,hC,hG⟩ := cuspRayWeakEuler_exists_classical hY.le (s*(1-s)) c g
    ((gamma0GlobalCuspConstantTerm_locallyIntegrable N r U).mono_set hsub)
    ((gamma0GlobalCuspConstantTermDerivative_locallyIntegrable N r u).mono_set hsub)
    (gamma0EnergyMass_global_constant_first_weak N r u hY)
    (gamma0EnergyMass_global_constant_derivative_weak_of_pencil N r (s*(1-s)) u F hu Y hY hF)
  have hpq : s≠1-s := by
    intro h
    have hre := congrArg Complex.re h
    simp only [Complex.sub_re,Complex.one_re] at hre
    linarith
  obtain ⟨A,B,hAB⟩ := cuspComplexEuler_solution_classification C G hY.le (s*(1-s)) s (1-s)
    (by ring) rfl hpq hC hG
  have hcAB : c=ᵐ[volume.restrict (Ioi Y)] fun y => A*(y:ℂ)^s+B*(y:ℂ)^(1-s) := by
    filter_upwards [hcC,ae_restrict_mem measurableSet_Ioi] with y hy hyY
    exact hy.trans (hAB y hyY)
  have ht : IntegrableOn (fun y : ℝ => ‖A*(y:ℂ)^s+B*(y:ℂ)^(1-s)‖^2/y^2) (Ioi Y) := by
    apply (gamma0GlobalCuspConstantTerm_integrable_energy N r U Y hY).congr
    filter_upwards [hcAB] with y hy
    change ‖c y‖^2/y^2=_
    rw [hy]
  have hA := cuspComplexEuler_tail_forces_plus_zero A B s (1-s) hY hs.le
    (gamma0Eisenstein_reflect_realPart hs) ht
  exact ⟨B,by simpa only [hA,zero_mul,zero_add] using hcAB⟩

theorem gamma0CompactForcingResolvent_normalized_outgoing_mode (N : ℕ) [NeZero N]
    (ψ : h2SmoothCompactSeeds) (A : Gamma0CompactResolventCutoff N ψ) (r : SL(2,ℤ))
    (s : ℂ) (hs : s∈gamma0EisensteinContinuationDomain) :
    ∃ B : ℂ, gamma0GlobalCuspConstantTerm N r
      (gamma0AmbientResolventFamily N (s*(1-s)) (gamma0SmoothSeedMass N ψ))
      =ᵐ[volume.restrict (Ioi A.height)] fun y =>
        B*((y/(gamma0CuspTrueWidth N r:ℝ):ℝ):ℂ)^(1-s) := by
  obtain ⟨B,hB⟩ := gamma0EnergyMass_outgoing_global_mode_of_pencil N r s hs.1
    (gamma0CompactForcingResolventEnergy N ψ s hs) (gamma0SmoothSeedMass N ψ)
    (gamma0CompactForcingResolventEnergy_pencil N ψ s hs) A.height A.pos (A.mass_tail_test_zero r)
  rw [gamma0CompactForcingResolventEnergy_mass N ψ s hs] at hB
  refine ⟨B*(gamma0CuspTrueWidth N r:ℂ)^(1-s),?_⟩
  filter_upwards [hB,ae_restrict_mem measurableSet_Ioi] with y hy hyA
  have hy0 : 0<y := A.pos.trans hyA
  have hw : (0:ℝ)<gamma0CuspTrueWidth N r := Nat.cast_pos.mpr (gamma0CuspTrueWidth_pos N r)
  have hn : (gamma0CuspTrueWidth N r:ℂ)^(1-s)≠0 :=
    Complex.cpow_ne_zero_iff.mpr (Or.inl (by exact_mod_cast (gamma0CuspTrueWidth_pos N r).ne'))
  rw [hy,Complex.ofReal_div,Complex.div_cpow_ofReal_nonneg hy0.le hw.le]
  simp only [Complex.ofReal_natCast]
  field_simp

end ArtinMatthews
