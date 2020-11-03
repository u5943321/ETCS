

(*display one + one as 2?*)

Theorem Thm4:
∀ss J X. ss∶ J → exp X (one + one) ⇒
       ∃a. is_subset a X ∧
           (∀x. x∶ one → X ⇒
                (is_mem x a X ⇔ ∃j. j∶ one → J ∧ (ev X (one + one)) o ⟨x,ss o j⟩ = i2 one one))
Proof                
rw[] >>
qabbrev_tac ‘s0 = (ev X (one + one)) o ⟨p1 X J, ss o p2 X J⟩’ >>
qabbrev_tac ‘i2t = (i2 one one) o (to1 (X× J))’ >>
‘s0∶ (X× J) → (one + one)’ by cheat >>
‘i2t∶ (X × J) → (one + one)’ by cheat >>
‘to1 (X × J)∶ (X× J) → one’ by metis_tac[ax1_1] >>
‘i2 one one∶ one → (one + one)’ by metis_tac[ax1_4] >> 
qabbrev_tac ‘k = eqa s0 i2t’ >>
qabbrev_tac ‘σ = eqo s0 i2t’ >>
‘k∶ σ → (X × J)’ by cheat >>
‘p1 X J o k∶ σ → X’ by cheat >>
drule mono_epi_fac >> strip_tac >>
rename [‘a∶ U → X’,‘q∶ σ → U’] >> qexists_tac ‘a’ >> rw[] (* 2 *)
>- (simp[is_subset_def] >> metis_tac[hom_def]) >>
‘∀j. j∶one → J ⇒ (ev X (one + one) ∘ ⟨x,ss ∘ j⟩ = i2 one one ⇔
                  s0 o ⟨x,j⟩ = i2 one one)’
  by
   (rw[] >>
    ‘ev X (one + one) ∘ ⟨x,ss ∘ j⟩ = s0 ∘ ⟨x,j⟩’ suffices_by metis_tac[] >>
    simp[Abbr‘s0’] >>
    ‘⟨x,ss ∘ j⟩∶ one → (X× (exp X (one + one)))’ by cheat >>
    ‘ev X (one + one)∶ (X× (exp X (one + one))) → (one + one)’ by metis_tac[ev_hom]>>
    ‘⟨x,j⟩∶ one → (X× J)’ by metis_tac[pa_hom] >>
    ‘⟨p1 X J,ss ∘ p2 X J⟩∶ (X×J) → (X× (exp X (one + one)))’ by cheat >>
    ‘(ev X (one + one) ∘ ⟨p1 X J,ss ∘ p2 X J⟩) ∘ ⟨x,j⟩ =
     ev X (one + one) ∘ ⟨p1 X J,ss ∘ p2 X J⟩ ∘ ⟨x,j⟩’ by metis_tac[compose_assoc]>>
    rw[] >>
    ‘⟨x,ss ∘ j⟩ = ⟨p1 X J,ss ∘ p2 X J⟩ ∘ ⟨x,j⟩’ suffices_by metis_tac[] >>
    ‘⟨x,ss ∘ j⟩∶ one → (X × exp X (one + one))’ by cheat >>
    ‘⟨p1 X J,ss ∘ p2 X J⟩ ∘ ⟨x,j⟩∶ one → (X × exp X (one + one))’
     by metis_tac[compose_hom] >>
    irule to_p_eq_applied >> qexistsl_tac [‘X’,‘exp X (one + one)’,‘one’] >>
    simp[] >> cheat) >>
‘is_mem x a X ⇔
        ∃j. j∶one → J ∧ s0 o ⟨x,j⟩  = i2 one one’ suffices_by metis_tac[] >>
rw[EQ_IMP_THM] (* 2 *)
>- (drule is_epi_surj >> strip_tac >>
   ‘∃xb0. xb0∶ one → U ∧ a o xb0 = x’ by (fs[is_mem_def] >> metis_tac[hom_def]) >>
   first_x_assum (qspecl_then [‘σ’,‘U’,‘xb0’] assume_tac) >> rfs[] >>
   rename [‘xb∶ one → σ’] >>
   qabbrev_tac ‘j = (p2 X J) o k o xb’ >>
   qexists_tac ‘j’ >>
   ‘(p2 X J)∶ (X × J) → J’ by metis_tac[p2_hom] >>
   ‘p2 X J ∘ k ∘ xb∶one → J’ by metis_tac[compose_hom] >> simp[] >>
   ‘j∶ one → J’ by metis_tac[compose_hom] >>
   ‘⟨x,j⟩∶ one → (X × J)’ by metis_tac[pa_hom] >>
   ‘k o xb∶ one → (X × J)’ by metis_tac[compose_hom] >>
   ‘⟨x,j⟩ = k o xb’
     by
      (irule to_p_eq_applied >> qexistsl_tac [‘X’,‘J’,‘one’] >> rw[] (* 2 *)
       >- (‘p1 X J ∘ ⟨a ∘ q ∘ xb,j⟩ = a o q o xb’ by metis_tac[p1_of_pa] >>
          rw[] >>
          ‘a o q = p1 X J o k’ suffices_by metis_tac[compose_assoc,p1_hom] >>
          metis_tac[])
       >- metis_tac[p2_of_pa]) >>
   ‘s0 o k = i2t o k’
     by (simp[Abbr‘k’] >> metis_tac[eq_equlity]) >>
   ‘i2t o k o xb = i2 one one’
     by cheat 
     (*cheat
      (simp[Abbr‘i2t’] >>
       ‘(i2 one one ∘ to1 (X × J)) ∘ k ∘ xb = i2 one one ∘ to1 (X × J) ∘ k ∘ xb’
        by (* metis_tac[compose_hom,compose_assoc] *) cheat>>
       ‘to1 (X × J) ∘ k ∘ xb = id one’ suffices_by metis_tac[id1,idR] >>
       irule to1_unique >> qexists_tac ‘one’ >> simp[id1] >>
       metis_tac[compose_hom])*) >>
   ‘s0 o ⟨x,j⟩ = s0 o k o xb’ by metis_tac[] >>
   ‘s0 ∘ k ∘ xb = (s0 ∘ k) ∘ xb’ by metis_tac[compose_assoc] >>
   ‘(s0 ∘ k) ∘ xb = (i2t ∘ k) o xb’ by metis_tac[] >>
   ‘s0 o ⟨x,j⟩  = i2 one one’ by metis_tac[compose_assoc] >>
   metis_tac[]) (*next is last case split*) >>
‘⟨x,j⟩∶ one → (X×J)’ by metis_tac[pa_hom] >>
‘i2t o ⟨x,j⟩ = i2 one one’ by cheat >>
‘k o eq_induce s0 i2t ⟨x,j⟩ = ⟨x,j⟩’
  by (simp[Abbr‘k’] >> metis_tac[eq_fac]) >>
‘(eq_induce s0 i2t ⟨x,j⟩)∶ one → σ’ by (simp[Abbr‘σ’] >> metis_tac[eq_induce_hom])>>
qabbrev_tac ‘xb = (eq_induce s0 i2t ⟨x,j⟩)’ >>
simp[is_mem_def,is_subset_def] >> strip_tac (* 2 *)
>- metis_tac[hom_def] >>
‘∃x0. x0∶one → U ∧ a ∘ x0 = x’ suffices_by metis_tac[hom_def] >>
qexists_tac ‘q o xb’ >> simp[] >> cheat
QED
   

