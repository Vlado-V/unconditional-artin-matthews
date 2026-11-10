module

public import ArtinMatthews.SpectralCuspBesselTransform
public import ArtinMatthews.SpectralResidualEigenbasis
public import ArtinMatthews.SpectralGamma0FourierEnergy
public import Mathlib.Analysis.RCLike.Sqrt
public import ArtinMatthews.SpectralAmbientEllipticPlane
public import ArtinMatthews.SpectralGamma0LocalFourierBessel
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

/-! Nonzero Fourier modes of every represented ambient eigenvector,
including vectors in the residual eigenspaces. -/

noncomputable section
open Set MeasureTheory Filter
open scoped MatrixGroups ContDiff

namespace ArtinMatthews

theorem gamma0EnergyEigen_fourier_bessel_ae (N : ℕ) [NeZero N]
    (v : gamma0EnergySpace N) (eig : ℝ) (hl : 0 ≤ eig)
    (hG : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n (gamma0EnergyInclusion N v)
      =ᵐ[volume.restrict (Ioi Y)] fun y => a *
        cuspBesselKernel (Complex.sqrt (1 / 4 - (eig : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n|) y := by
  obtain ⟨u, hu, hrep, hp, hEq⟩ :=
    gamma0AmbientEigen_plane_smooth_periodic_classical N v eig hl hG r Y hY
  exact gamma0CuspLocalFourier_bessel_ae N r Y hY n hn v u hu hrep
    (fun x t hx hxt ht => hp (x, t) ⟨hx, hxt, ht⟩) eig hEq

theorem gamma0AmbientEigen_fourier_bessel_ae (N : ℕ) [NeZero N]
    (eig : ℝ) (hl : 0 ≤ eig) (m : Gamma0RegionL2 N)
    (hG : gamma0Green N m = (((eig + 1)⁻¹ : ℝ) : ℂ) • m)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n m
      =ᵐ[volume.restrict (Ioi Y)] fun y => a *
        cuspBesselKernel (Complex.sqrt (1 / 4 - (eig : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n|) y := by
  obtain ⟨v, hv, _⟩ := gamma0AmbientEnergyEigenspace_energy_pencil N eig hl m
    ((mem_gamma0AmbientEnergyEigenspace_iff N eig m).mpr hG)
  have hGv : gamma0Green N (gamma0EnergyInclusion N v) =
      (((eig + 1)⁻¹ : ℝ) : ℂ) • gamma0EnergyInclusion N v := by
    rw [hv]
    exact hG
  simpa only [hv] using gamma0EnergyEigen_fourier_bessel_ae N v eig hl hGv r Y hY n hn

theorem gamma0AmbientEigen_operator_iff_green (N : ℕ) [NeZero N]
    (eig : ℝ) (hl : 0 ≤ eig) (m : Gamma0RegionL2 N) :
    (m, (((eig + 1 : ℝ) : ℂ) • m)) ∈ (gamma0MassEnergyOperator N).graph ↔
      gamma0Green N m = (((eig + 1)⁻¹ : ℝ) : ℂ) • m := by
  rw [gamma0MassEnergyOperator_graph, map_smul, Complex.ofReal_inv]
  let a : ℂ := ((eig + 1 : ℝ) : ℂ)
  have ha : a ≠ 0 := Complex.ofReal_ne_zero.mpr (by linarith)
  change a • gamma0Green N m = m ↔ gamma0Green N m = a⁻¹ • m
  constructor
  · intro h
    calc
      gamma0Green N m = a⁻¹ • (a • gamma0Green N m) := by
        rw [smul_smul, inv_mul_cancel₀ ha, one_smul]
      _ = a⁻¹ • m := congrArg (fun x : Gamma0RegionL2 N => a⁻¹ • x) h
  · intro h
    rw [h, smul_smul, mul_inv_cancel₀ ha, one_smul]

theorem gamma0AmbientOperatorEigen_fourier_bessel_ae (N : ℕ) [NeZero N]
    (eig : ℝ) (hl : 0 ≤ eig) (m : Gamma0RegionL2 N)
    (hm : (m, (((eig + 1 : ℝ) : ℂ) • m)) ∈ (gamma0MassEnergyOperator N).graph)
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n m
      =ᵐ[volume.restrict (Ioi Y)] fun y => a *
        cuspBesselKernel (Complex.sqrt (1 / 4 - (eig : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n|) y :=
  gamma0AmbientEigen_fourier_bessel_ae N eig hl m
    ((gamma0AmbientEigen_operator_iff_green N eig hl m).mp hm) r Y hY n hn

theorem gamma0ResidualEigenbasis_fourier_bessel_ae (N : ℕ) [NeZero N]
    (eig : Ici (0 : ℝ)) (j : Fin (Module.finrank ℂ (gamma0ResidualEnergyEigenspace N eig)))
    (r : SL(2, ℤ)) (Y : ℝ) (hY : 0 < Y) (n : ℤ) (hn : n ≠ 0) :
    ∃ a : ℂ, gamma0CuspFourierCoefficient N r Y hY n (gamma0ResidualEigenbasis N eig j).val
      =ᵐ[volume.restrict (Ioi Y)] fun y => a *
        cuspBesselKernel (Complex.sqrt (1 / 4 - ((eig : ℝ) : ℂ)))
          (|cuspFourierFrequency (N : ℝ) n|) y :=
  gamma0AmbientEigen_fourier_bessel_ae N eig eig.property _
    (gamma0ResidualEigenbasis_green N eig j) r Y hY n hn

end ArtinMatthews
