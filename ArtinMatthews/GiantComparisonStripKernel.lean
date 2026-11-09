module

public import ArtinMatthews.GiantComparisonStripEquiv
public import ArtinMatthews.GiantComparisonStripMass
public import ArtinMatthews.GiantCharacterGraph


set_option backward.privateInPublic true
@[expose] public section

/-! The literal physical comparison coefficient carries one half-damping
at each endpoint. Pairing with the endpoint vectors supplies the other
halves. The quotient removes only the copied product and its phase. -/
namespace ArtinMatthews
open Finset
open scoped BigOperators ComplexConjugate
noncomputable section
attribute [local instance] Classical.propDecidable

variable {J : Type*} [Fintype J] {P : J → Finset ℕ} {k ell N m : ℕ}
  {C : J → Finset (Fin k)} {Z Z' : Finset ℕ}

def giantComparisonPhysicalSummand (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    (s : GiantTwoSidedEndpointState P (k+ell) Z)
    (t : GiantTwoSidedEndpointState P (k+ell) Z')
    (aux : GiantTwoSidedPatternAuxiliary P C) : ℂ :=
  let n := s.val.1.val
  let n' := t.val.1.val
  let D := giantTwoSidedPatternCopiedProduct C s.val.2*giantTwoSidedPatternAuxiliaryProduct aux
  (markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell) : ℂ) *
    giantTwoSidedPatternPhysicalCoefficient 1 q 0 K s t aux *
    (Ψ ((n:ℝ)/(x*(D:ℝ)))/(n:ℂ)) *
    F n * (conj (χ D)*χ n') * G n' *
    (giantTwoSidedEndpointDamping P (k+ell) q n : ℂ) *
    (giantTwoSidedEndpointDamping P (k+ell) q n' : ℂ)

def giantComparisonPositionKernel (x : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ) (d w : ℕ) : ℂ :=
  (Ψ ((w:ℝ)/(x*(d:ℝ)))/(w:ℂ))*F w*(conj (χ d)*χ (w+d:ℕ))*G (w+d)

def giantComparisonSharedSummand (x q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    {aux : GiantTwoSidedPatternAuxiliary P C}
    (a : GiantComparisonSharedEdge P C ell N Z Z' aux) : ℂ :=
  let c := a.val.1
  let w := a.val.2.1.val
  let b := a.val.2.2.1
  let b' := a.val.2.2.2
  let D := giantComparisonSharedProduct c
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  ((giantComparisonSharedMass c*giantTwoSidedPatternFreshMass P C ell^2:ℝ):ℂ) *
    (giantTwoSidedPatternAuxiliaryMass aux:ℂ) *
    K (giantComparisonJoinLabels c b) (giantComparisonJoinLabels c b') aux *
    giantComparisonPositionKernel x Ψ χ F G d w *
    ((giantTwoSidedEndpointDamping P (k+ell) q (D*w))^2:ℝ) *
    ((giantTwoSidedEndpointDamping P (k+ell) q (D*(w+d)))^2:ℝ)

theorem giantComparisonPhysicalSummand_eq_shared (hP : ∀ j p, p ∈ P j → p.Prime)
    {x : ℝ} (hx : 0 < x) (q : ℝ) (Ψ : ℝ → ℂ)
    (χ : DirichletCharacter ℂ m) (F G : ℕ → ℂ)
    (K : GiantTwoSidedPatternCoefficient P C ell)
    {aux : GiantTwoSidedPatternAuxiliary P C}
    (a : GiantComparisonSharedEdge P C ell N Z Z' aux)
    (hF : F (giantComparisonSharedProduct a.val.1*a.val.2.1.val) = F a.val.2.1.val)
    (hG : G (giantComparisonSharedProduct a.val.1*
      (a.val.2.1.val+giantTwoSidedPatternAuxiliaryProduct aux)) =
        G (a.val.2.1.val+giantTwoSidedPatternAuxiliaryProduct aux))
    (hc : (giantComparisonSharedProduct a.val.1).Coprime m) :
    giantComparisonPhysicalSummand x q Ψ χ F G K
        (giantComparisonShared_to_physical a).val.1 (giantComparisonShared_to_physical a).val.2 aux =
      giantComparisonSharedSummand x q Ψ χ F G K a := by
  let e := giantComparisonShared_to_physical a
  let s := e.val.1
  let t := e.val.2
  let c := a.val.1
  let w := a.val.2.1.val
  let b := a.val.2.2.1
  let b' := a.val.2.2.2
  let D := giantComparisonSharedProduct c
  let d := giantTwoSidedPatternAuxiliaryProduct aux
  let σ := markedPhysicalMass (fun j => bandReciprocalMass (P j)) (k+ell)
  let B := giantTwoSidedPatternFreshMass P C ell
  let μ := giantComparisonSharedMass c
  let ν := giantTwoSidedPatternAuxiliaryMass aux
  let jₛ := giantComparisonJoinLabels c b
  let jₜ := giantComparisonJoinLabels c b'
  let δ (n : ℕ) := giantTwoSidedEndpointDamping P (k+ell) q n
  have hn : s.val.1.val = D*w := rfl
  have hn' : t.val.1.val = D*(w+d) := rfl
  have hs : s.val.2 = jₛ := rfl
  have ht : t.val.2 = jₜ := rfl
  have hcopied : giantTwoSidedPatternCopiedProduct C jₛ = D :=
    giantComparisonSharedProduct_join c b
  have hcoef : giantTwoSidedPatternPhysicalCoefficient 1 q 0 K s t aux =
      (ν:ℂ)*(B:ℂ)*K jₛ jₜ aux*(δ (D*w):ℂ)*(δ (D*(w+d)):ℂ) := by
    rw [giantTwoSidedPatternPhysicalCoefficient, ite_eq_left e.property, hs, ht, hn, hn']
    simp only [Complex.ofReal_zero, zero_mul, Complex.cpow_zero, mul_one]
    rfl
  have hD : (D:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (giantComparisonSharedProduct_pos hP c).ne'
  have hd : (d:ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (show 0 < d from
    prod_pos fun j _ => prod_pos fun i _ => (hP j _ (aux j i).property).pos).ne'
  have harg : ((D*w:ℕ):ℝ)/(x*((D*d:ℕ):ℝ)) = (w:ℝ)/(x*(d:ℝ)) := by
    push_cast
    field_simp [hD, hx.ne', hd]
  have hχ : conj (χ (D*d:ℕ))*χ (D*(w+d):ℕ) = conj (χ d)*χ (w+d:ℕ) :=
    by simpa only [Nat.cast_mul] using giant_character_shared_factor χ D d (w+d) hc
  have hmass : (σ:ℂ)*(B:ℂ)/(D:ℂ) = ((μ*B^2:ℝ):ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_natCast, ← Complex.ofReal_div]
    exact congrArg (fun z : ℝ => (z:ℂ)) (giantComparisonStrip_mass_factor C ell c)
  have hscale :
      (σ:ℂ)*(B:ℂ)*(Ψ ((w:ℝ)/(x*(d:ℝ)))/((D*w:ℕ):ℂ)) =
        ((μ*B^2:ℝ):ℂ)*(Ψ ((w:ℝ)/(x*(d:ℝ)))/(w:ℂ)) := by
    rw [← hmass, Nat.cast_mul, div_mul_eq_div_div]
    ring
  change F (D*w) = F w at hF
  change G (D*(w+d)) = G (w+d) at hG
  calc
    _ = ((σ:ℂ)*(B:ℂ)*(Ψ ((w:ℝ)/(x*(d:ℝ)))/((D*w:ℕ):ℂ))) *
        ((ν:ℂ)*K jₛ jₜ aux*F w*(conj (χ d)*χ (w+d:ℕ))*G (w+d)*
          ((δ (D*w))^2:ℝ)*((δ (D*(w+d)))^2:ℝ)) := by
      change (σ:ℂ)*giantTwoSidedPatternPhysicalCoefficient 1 q 0 K s t aux *
          (Ψ ((s.val.1.val:ℝ)/(x*((giantTwoSidedPatternCopiedProduct C s.val.2*d:ℕ):ℝ)))/
            (s.val.1.val:ℂ)) *
          F s.val.1.val *
          (conj (χ (giantTwoSidedPatternCopiedProduct C s.val.2*d:ℕ))*χ t.val.1.val) *
          G t.val.1.val * (δ s.val.1.val:ℂ)*(δ t.val.1.val:ℂ) = _
      rw [hcoef, hs, hcopied, hn, hn', harg, hF, hG, hχ]
      simp only [Complex.ofReal_pow]
      ring
    _ = _ := by
      rw [hscale]
      change ((μ*B^2:ℝ):ℂ)*(Ψ ((w:ℝ)/(x*(d:ℝ)))/(w:ℂ)) *
          ((ν:ℂ)*K jₛ jₜ aux*F w*(conj (χ d)*χ (w+d:ℕ))*G (w+d)*
            ((δ (D*w))^2:ℝ)*((δ (D*(w+d)))^2:ℝ)) =
        ((μ*B^2:ℝ):ℂ)*(ν:ℂ)*K jₛ jₜ aux*giantComparisonPositionKernel x Ψ χ F G d w*
          ((δ (D*w))^2:ℝ)*((δ (D*(w+d)))^2:ℝ)
      unfold giantComparisonPositionKernel
      ring

end
end ArtinMatthews
