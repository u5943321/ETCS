Theorem pred_exist:
∃p. p∶ N → N ∧ p o z = z ∧ p o s = id N
Proof
‘z∶ one → N’ by metis_tac[ax3] >>
‘p1 N N∶ N × N → N’ by metis_tac[p1_hom] >>
drule_all Thm1_case_1 >> metis_tac[EXISTS_UNIQUE_ALT,p1_of_pa,id1]
QED


(*0 is not a successor*)

Theorem Thm2_1:
∀n. n∶ one → N ⇒ (s o n) ≠ z
Proof
rw[] >> SPOSE_NOT_THEN ASSUME_TAC >>
‘∃p. p∶ N → N ∧ p o z = z ∧ p o s = id N’ by metis_tac[pred_exist] >>
‘n = (p o s) o n’ by metis_tac[idL] >>
‘s∶ N → N’ by metis_tac[ax3] >>
‘(p o s) o n = p o s o n’ by metis_tac[compose_assoc] >>
‘p o s o n = p o z’ by metis_tac[] >>
‘n = z’ by metis_tac[] >>
‘∀X t. t∶ X → X ⇒ t = id X’ suffices_by metis_tac[distinct_endo_exists] >>
rw[] >>
irule fun_ext >> qexistsl_tac [‘X’,‘X’] >> rw[] >>
drule_all ax3_conj2 >> rw[] >>
‘t o a = t o (N_ind a t) o z’ by metis_tac[] >>
‘t o (N_ind a t) o z = (t o (N_ind a t)) o z’ by metis_tac[compose_assoc] >>
‘t o (N_ind a t) o z = ((N_ind a t) o s) o z’ by metis_tac[] >>
‘((N_ind a t) o s) o z = (N_ind a t) o s o z’ by metis_tac[compose_assoc] >>
‘(N_ind a t) o s o z = (N_ind a t) o z’ by metis_tac[] >>
metis_tac[idL]
QED


(*s is a mono*)

Theorem Thm2_2:
is_mono s
Proof
irule post_inv_mono >>
‘∃p. p∶ N → N ∧ p o z = z ∧ p o s = id N’ by metis_tac[pred_exist] >>
qexistsl_tac [‘N’,‘N’,‘p’] >> 
‘s∶ N → N’ by metis_tac[ax3] >>
metis_tac[]
QED


(*induction *)


Theorem Thm2_3_alt:
∀A a s' z'. a∶ A → N ∧ is_mono a ∧ s'∶ A → A ∧ z'∶ one → A ∧
            a o s' = s o a ∧ a o z' = z ⇒ A ≅ N
Proof            
rw[] >>
drule_all ax3_conj2 >> rw[] >>
‘a o (N_ind z' s') = id N’
  by
   (irule comm_with_s_id >>
   ‘a ∘ N_ind z' s'∶N → N’ by metis_tac[compose_hom] >>
   ‘(N_ind z' s')∶N → A ∧ (N_ind z' s') ∘ z = z' ∧
    (N_ind z' s') ∘ s = s' ∘ (N_ind z' s')’ by metis_tac[] >>
   simp[] >>
   ‘z∶ one → N’ by metis_tac[ax3] >>
   ‘(a ∘ N_ind z' s') ∘ z = a ∘ N_ind z' s' ∘ z’
     by metis_tac[compose_assoc] >>
   ‘a ∘ N_ind z' s' ∘ z = a o z'’ by metis_tac[] >>
   simp[] >>
   metis_tac[ax3,compose_assoc]) >>
‘∃f. f∶ A → N ∧ is_iso f’ suffices_by metis_tac[are_iso_is_iso] >>
qexists_tac ‘a’ >> rw[] >> irule mono_epi_is_iso >>
rw[] >> irule pre_inv_epi >> qexistsl_tac [‘A’,‘N’,‘N_ind z' s'’] >>
rw[] >> metis_tac[]
QED

Theorem ind_factorization:
∀A a. a∶ A → N ∧ is_mono a ∧ (∀n. is_mem n a N ⇒ is_mem (s ∘ n) a N) ⇒
        ∃t. t∶ A → A ∧ a o t = s o a
Proof
cheat
QED                
        
Theorem Thm2_3:        
∀A a. is_subset a N ∧ (∀n. is_mem n a N ⇒ is_mem (s o n) a N) ∧
    is_mem z a A ⇒ dom a ≅ N
Proof
rw[] >> irule Thm2_3_alt >> fs[is_subset_def] >>
‘a∶ dom a → N’ by metis_tac[hom_def] >>
qabbrev_tac ‘A = dom a’ >>
drule ind_factorization >> fs[is_mem_def] >> metis_tac[]
QED

     
