module

public import ArtinMatthews.SourcePrincipalKernel


set_option backward.privateInPublic true
@[expose] public section

/-! Exact singleton-residue conventions for absent source moduli. -/
namespace ArtinMatthews.SourceCRTNormalization

open NumberField IsDedekindDomain ArtinMatthews.SIntegerPrincipalization
open ArtinMatthews.SIntegerQuotient ArtinMatthews.StandardAdelic
open scoped NumberField Classical
noncomputable section
variable {K : Type} [Field K] [NumberField K]
variable (S₀ : Finset (HeightOneSpectrum (𝓞 K)))

theorem sourceSpanOne_tsum (z : ℂ) :
    (∑' _d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)}, z) = z := by
  let : Subsingleton ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)}) :=
    Ideal.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
  let : Unique ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)}) :=
    ⟨⟨0⟩, fun _ => Subsingleton.elim _ _⟩
  let : Fintype ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)}) := Fintype.ofFinite _
  rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_unique, one_nsmul]

theorem principalSourceKernel_outer_one (B : PrincipalIntegerRing S₀) (hB : B ≠ 0)
    (H : PrincipalIntegerRing S₀) (Z : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {B}) → ℂ) :
    principalSourceKernel S₀ 1 B one_ne_zero hB H (fun _ => 1) Z =
      ∑' v : (PrincipalIntegerRing S₀) ⧸ Ideal.span {B},
        Z v * sIntegerQuotientPhase K (principalizingSet S₀) B hB (Ideal.Quotient.mk _ H * v) := by
  let : Subsingleton ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)}) :=
    Ideal.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
  have hrep : ∀ d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)},
      Ideal.Quotient.mk (Ideal.span {(1 : PrincipalIntegerRing S₀)}) 0 = d := fun _ => Subsingleton.elim _ _
  unfold principalSourceKernel
  rw [quotientCongruenceKernel_representatives _ _ B H (Ideal.mem_span_singleton_self B) _ _ _
    (fun _ => 0) Quotient.out hrep (fun v => Ideal.Quotient.mk_out v)]
  have hm : H ∈ (Ideal.span {(1 : PrincipalIntegerRing S₀)} : Ideal (PrincipalIntegerRing S₀)) := by simp
  simp only [mul_zero, sub_zero, ite_eq_left hm, one_mul]
  rw [sourceSpanOne_tsum]
  apply tsum_congr
  intro v
  have he : Ideal.Quotient.mk (Ideal.span {B}) H * v =
      Ideal.Quotient.mk _ (H * Quotient.out v) := by rw [map_mul, Ideal.Quotient.mk_out]
  rw [he, sourceProductPhase_mk, sIntegerQuotientPhase_mk]
  congr 1
  congr 1
  change ((H * Quotient.out v : PrincipalIntegerRing S₀) : K) / ((1 : K) * (B : K)) =
    ((H * Quotient.out v : PrincipalIntegerRing S₀) : K) / (B : K)
  rw [one_mul]

theorem principalSourceKernel_inner_one (A : PrincipalIntegerRing S₀) (hA : A ≠ 0)
    (H : PrincipalIntegerRing S₀) (W : ((PrincipalIntegerRing S₀) ⧸ Ideal.span {A}) → ℂ) :
    principalSourceKernel S₀ A 1 hA one_ne_zero H W (fun _ => 1) =
      ∑' d : (PrincipalIntegerRing S₀) ⧸ Ideal.span {A},
        if H - Quotient.out d ∈ Ideal.span {A} then W d else 0 := by
  let : Subsingleton ((PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)}) :=
    Ideal.Quotient.subsingleton_iff.mpr Ideal.span_singleton_one
  have hrep : ∀ v : (PrincipalIntegerRing S₀) ⧸ Ideal.span {(1 : PrincipalIntegerRing S₀)},
      Ideal.Quotient.mk (Ideal.span {(1 : PrincipalIntegerRing S₀)}) 0 = v := fun _ => Subsingleton.elim _ _
  unfold principalSourceKernel
  rw [quotientCongruenceKernel_representatives _ _ 1 H
    (Ideal.subset_span (by simp)) _ _ _ Quotient.out (fun _ => 0)
    (fun d => Ideal.Quotient.mk_out d) hrep]
  simp only [one_mul, mul_zero, map_zero, AddChar.map_zero_eq_one, mul_one]
  apply tsum_congr
  intro d
  exact sourceSpanOne_tsum S₀ _

theorem principalSourceKernel_one_one (H : PrincipalIntegerRing S₀) :
    principalSourceKernel S₀ 1 1 one_ne_zero one_ne_zero H (fun _ => 1) (fun _ => 1) = 1 := by
  rw [principalSourceKernel_inner_one]
  simp only [Ideal.span_singleton_one, Submodule.mem_top, ite_true]
  convert sourceSpanOne_tsum S₀ 1 using 1

end
end ArtinMatthews.SourceCRTNormalization
