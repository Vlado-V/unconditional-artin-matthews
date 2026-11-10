module

public import ArtinMatthews.SixthExteriorPowerClasses


set_option backward.privateInPublic true
@[expose] public section

/-! The genuine class map from reduced exterior rows modulo sixth powers
of exterior S-units to global sixth-power classes. Its injectivity is
proved from principal-ideal valuations; no class-map premise is used. -/
namespace ArtinMatthews
open IsDedekindDomain
open scoped NumberField
noncomputable section

variable {K : Type*} [Field K] [NumberField K]

def globalSixthPowerSubgroup : Subgroup Kˣ := (powMonoidHom (α := Kˣ) 6).range

def exteriorSixthPowerSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) : Subgroup Kˣ :=
  (exteriorUnitSubgroup S).map (powMonoidHom (α := Kˣ) 6)

omit [NumberField K] in
theorem mem_globalSixthPowerSubgroup (u : Kˣ) :
    u ∈ globalSixthPowerSubgroup ↔ ∃ t : Kˣ, t^6=u := Iff.rfl

theorem mem_exteriorSixthPowerSubgroup (S : Finset (HeightOneSpectrum (𝓞 K))) (u : Kˣ) :
    u ∈ exteriorSixthPowerSubgroup S ↔ ∃ t : exteriorUnitSubgroup S, (t:Kˣ)^6=u := by
  constructor
  · rintro ⟨t,ht,he⟩
    exact ⟨⟨t,ht⟩,he⟩
  · rintro ⟨t,he⟩
    exact ⟨t,t.2,he⟩

theorem exteriorSixthPowerSubgroup_le_global (S : Finset (HeightOneSpectrum (𝓞 K))) :
    exteriorSixthPowerSubgroup S ≤ globalSixthPowerSubgroup := by
  intro u hu
  obtain ⟨t,ht⟩ := (mem_exteriorSixthPowerSubgroup S u).mp hu
  exact (mem_globalSixthPowerSubgroup u).mpr ⟨t,ht⟩

/-- On reduced rows, equality modulo the global sixth powers is exactly
equality modulo the sixth powers of actual exterior S-units. -/
theorem exteriorSixthReduced_class_eq_iff
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u v : Kˣ)
    (hu : ExteriorSixthReduced S u) (hv : ExteriorSixthReduced S v) :
    QuotientGroup.mk' (exteriorSixthPowerSubgroup S) u=
        QuotientGroup.mk' (exteriorSixthPowerSubgroup S) v ↔
      QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) u=
        QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) v := by
  change ((u : Kˣ ⧸ exteriorSixthPowerSubgroup S) = v) ↔
    ((u : Kˣ ⧸ globalSixthPowerSubgroup) = v)
  rw [QuotientGroup.eq_iff_div_mem,QuotientGroup.eq_iff_div_mem]
  constructor
  · exact fun h => exteriorSixthPowerSubgroup_le_global S h
  · intro h
    obtain ⟨t,ht⟩ := (mem_globalSixthPowerSubgroup (u/v)).mp h
    obtain ⟨s,hs⟩ := (exteriorSixthReduced_power_iff S u v hu hv).mp ⟨t,ht.symm⟩
    exact (mem_exteriorSixthPowerSubgroup S (u/v)).mpr ⟨s,hs.symm⟩

theorem exteriorSixthReduced_global_class_valuations
    (S : Finset (HeightOneSpectrum (𝓞 K))) (u v : Kˣ)
    (hu : ExteriorSixthReduced S u) (hv : ExteriorSixthReduced S v)
    (h : QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) u=
      QuotientGroup.mk' (globalSixthPowerSubgroup (K := K)) v) :
    ∀ p, p ∉ S → exteriorPrincipalValuation p u=exteriorPrincipalValuation p v := by
  have hm : u/v ∈ globalSixthPowerSubgroup := QuotientGroup.eq_iff_div_mem.mp h
  obtain ⟨t,ht⟩ := (mem_globalSixthPowerSubgroup (u/v)).mp hm
  exact (exteriorSixthReduced_ratio_root S u v t hu hv ht.symm).1

abbrev ExteriorSixthReducedRow (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  {u : Kˣ // ExteriorSixthReduced S u}

/-- The relation uses the actual S-unit-power quotient, independently of
the global sixth-power quotient to which the final map will descend. -/
def exteriorReducedPowerSetoid (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Setoid (ExteriorSixthReducedRow S) where
  r u v := QuotientGroup.mk' (exteriorSixthPowerSubgroup S) u.1=
    QuotientGroup.mk' (exteriorSixthPowerSubgroup S) v.1
  iseqv := ⟨fun _ => rfl,fun h => h.symm,fun h₁ h₂ => h₁.trans h₂⟩

theorem exteriorReducedPowerSetoid_iff (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u v : ExteriorSixthReducedRow S) :
    (exteriorReducedPowerSetoid S).r u v ↔
      ∃ t : exteriorUnitSubgroup S, u.1/v.1=(t:Kˣ)^6 := by
  change ((u.1 : Kˣ ⧸ exteriorSixthPowerSubgroup S) = v.1) ↔ _
  rw [QuotientGroup.eq_iff_div_mem,mem_exteriorSixthPowerSubgroup]
  constructor <;> rintro ⟨t,ht⟩ <;> exact ⟨t,ht.symm⟩

abbrev ExteriorSixthReducedClasses (S : Finset (HeightOneSpectrum (𝓞 K))) :=
  Quotient (exteriorReducedPowerSetoid S)

def exteriorReducedPowerClassMap (S : Finset (HeightOneSpectrum (𝓞 K))) :
    ExteriorSixthReducedClasses S → Kˣ ⧸ globalSixthPowerSubgroup :=
  Quotient.lift (fun u : ExteriorSixthReducedRow S =>
    QuotientGroup.mk' globalSixthPowerSubgroup u.1)
    (fun u v h => (exteriorSixthReduced_class_eq_iff S u.1 v.1 u.2 v.2).mp h)

theorem exteriorReducedPowerClassMap_mk (S : Finset (HeightOneSpectrum (𝓞 K)))
    (u : ExteriorSixthReducedRow S) :
    exteriorReducedPowerClassMap S (Quotient.mk (exteriorReducedPowerSetoid S) u)=
      QuotientGroup.mk' globalSixthPowerSubgroup u.1 := rfl

/-- The natural reduced-row class map is injective. The proof compares
representatives through the actual exterior valuation calculation. -/
theorem exteriorReducedPowerClassMap_injective (S : Finset (HeightOneSpectrum (𝓞 K))) :
    Function.Injective (exteriorReducedPowerClassMap S) := by
  intro a b
  refine Quotient.inductionOn₂ a b ?_
  intro u v h
  apply Quotient.sound
  exact (exteriorSixthReduced_class_eq_iff S u.1 v.1 u.2 v.2).mpr h

end
end ArtinMatthews
