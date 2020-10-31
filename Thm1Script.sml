
Overload product_obj = “λA B. po A B”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "×"], 
                  term_name = "product_obj", paren_style = OnlyIfNecessary}

Overload exp_notation = “λB A. exp A B”
val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Infix (NONASSOC,450), 
                  pp_elements = [TOK "^"], 
                  term_name = "exp_notation", paren_style = OnlyIfNecessary}

(*why HOL cannot recognize this notation?*)
          
(*why the three lines does not work...?*)


val _ = add_rule {block_style = (AroundEachPhrase, (PP.CONSISTENT, 0)),
                  fixity = Closefix, 
                  pp_elements = [TOK "⟨", TM, TOK ",",TM, TOK "⟩"], 
                  term_name = "pa", paren_style = OnlyIfNecessary}

                  


Theorem Thm1_case_1:
∀B g h. g∶ one → B ∧ h∶ po N B → B ⇒
        ∃!f. f∶ N → B ∧ f o z = g ∧ f o s = h o ⟨id N, f⟩
Proof
cheat
QED
                
Theorem Thm1_comm_eq_left:
∀A B f g. g∶ A → B ∧ f∶ A×N → B ⇒
          (tp f o z = tp (g o (p1 A one)) ⇔
           f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one))
Proof
cheat
QED

Theorem Thm1_comm_eq_right:
∀A B f h. f∶ A× N → B ∧ h∶ (A×N)×B → B ⇒
          (h o ⟨id (A×N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩ ⇔
           tp (h o
                ⟨⟨p1 A (N×(exp A B))
                  ,(p1 N (exp A B)) o (p2 A (N×(exp A B)))⟩,
                (ev A B) o ⟨p1 A (N×(exp A B)),
                            (p2 N (exp A B) o (p2 A (N×(exp A B))))⟩⟩

           ) o  ⟨id N,tp f⟩
        = (tp f o s))
Proof
rw[] >>
qabbrev_tac ‘l = ⟨⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩,ev A B ∘
           ⟨p1 A (N×(exp A B)),p2 N (exp A B) ∘ p2 A (N×(exp A B))⟩⟩’ >>
‘(h ∘ ⟨id (A×N),f⟩)∶ A×N → B’ by cheat >>
‘tp (h ∘ l) ∘ ⟨id N,tp f⟩ ∶ N → exp A B’ by cheat >>
‘tp (h ∘ ⟨id (A×N),f⟩) =
 tp (h ∘
           ⟨⟨p1 A (N×(exp A B)),p1 N (exp A B) ∘ p2 A (N×(exp A B))⟩,(ev A B) ∘
           ⟨p1 A (N×(exp A B)),p2 N (exp A B) ∘ p2 A (N×(exp A B))⟩⟩) ∘ ⟨id N,tp f⟩
 ’ by
    (‘’
    )
    
‘tp (h ∘ l) ∘ ⟨id N,tp f⟩ = tp (h ∘ ⟨id (A×N),f⟩)’
 suffices_by metis_tac[] >>
irule is_tp >> qexistsl_tac [‘A’,‘B’,‘N’] >> rw[] >>
‘⟨p1 A N,(tp (h ∘ l) ∘ ⟨id N,tp f⟩) ∘ p2 A N⟩ =
 ⟨p1 A (N× (exp A B)), (tp (h ∘ l)) o p2 A (N× (exp A B))⟩ o
 ⟨p1 A N, ⟨id N,tp f⟩ o p2 A N⟩’ by cheat (*lemma for this pattern*) >>
simp[] >>
‘ev A B ∘ ⟨p1 A (N×(exp A B)),tp (h ∘ l) ∘ p2 A (N×(exp A B))⟩ = h o l’
  by cheat >>
‘ev A B ∘ ⟨p1 A (N×(exp A B)),tp (h ∘ l) ∘ p2 A (N×(exp A B))⟩ ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
 (ev A B ∘ ⟨p1 A (N×(exp A B)),tp (h ∘ l) ∘ p2 A (N×(exp A B))⟩) ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩’ by cheat >> fs[] >>
‘l o ⟨p1 A N,⟨id N,tp f⟩ o p2 A N⟩ =  ⟨id (A×N),f⟩’ suffices_by cheat >>
‘l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩∶ A× N → ((A×N)×B )∧
 ⟨id (A×N),f⟩∶ A×N → ((A×N)×B)’ by cheat >>
(*lemma on equality between iterated product*)
irule iterated_p_eq_applied >>
qexistsl_tac [‘A’,‘N’,‘B’,‘A×N’] >> rw[] (* 3 *)
>- ‘(p1 (A×N) B) o l =
    ⟨p1 A (N×(pow A B)),p1 N (pow A B) ∘ p2 A (N×(pow A B))⟩’
    by cheat >>
   ‘(p1 A N) o ⟨p1 A (N×(pow A B)),p1 N (pow A B) ∘ p2 A (N×(pow A B))⟩=
    p1 A (N×(pow A B))’ by cheat >>
   ‘(p1 A (N×(pow A B))) o ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ =
        p1 A N ∘ p1 (A×N) B ∘ ⟨id (A×N),f⟩’ suffices_by cheat >>
   (*LHS = RHS = p1 A N*) cheat
>- (*p2 A N*)   
>- ‘p2 (A×N) B ∘ l =
    ev A B ∘
           ⟨p1 A (N×(pow A B)),p2 N (pow A B) ∘ p2 A (N×(pow A B))⟩’
     by cheat >>
   ‘p2 (A×N) B ∘ l ∘ ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ = f’
     suffices_by cheat >>
   ‘⟨p1 A (N×pow A B),p2 N (pow A B) ∘ p2 A (N×pow A B)⟩ ∘
        ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩∶ (A×N) → (A× (exp A B)) ∧ 
        ⟨p1 A N,tp f ∘ p2 A N⟩∶(A×N) → (A× (exp A B))’ by cheat >>
   ‘⟨p1 A (N×pow A B),p2 N (pow A B) ∘ p2 A (N×pow A B)⟩ o
    ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩  =
    ⟨p1 A N,(tp f) o p2 A N⟩’ by
    irule to_p_eq_applied >>
    qexistsl_tac [‘A’,‘exp A B’,‘A×N’] >> rw[] (* 2 *)
    >- (*p1 A N*)
    >- (*RHS (tp f ∘ p2 A N)
         LHS ... *)
       ‘p2 A (exp A B) ∘ ⟨p1 A (N×pow A B),p2 N (pow A B) ∘ p2 A (N×pow A B)⟩ = p2 N (pow A B) ∘ p2 A (N×pow A B)’ by cheat >>
       ‘p2 N (pow A B) ∘ p2 A (N×pow A B) o ⟨p1 A N,⟨id N,tp f⟩ ∘ p2 A N⟩ = (tp f ∘ p2 A N)’ suffices_by cheat >>
       ‘p2 N (pow A B) o ⟨id N,tp f⟩ ∘ p2 A N = ⟨id N,tp f⟩ ∘ p2 A N’
        by cheat
   

cheat >>

‘(tp f o s)∶ N → exp A B’ by cheat >>
‘tp (f ∘ ⟨p1 A N,s ∘ p2 A N⟩) ∶ N → exp A B’ by cheat >>
‘f ∘ ⟨p1 A N,s ∘ p2 A N⟩∶A×N → B’ by cheat
‘tp (f ∘ ⟨p1 A N,s ∘ p2 A N⟩) =
 tp f o s’
 by
  (‘(ev A B) o ⟨p1 A N,(tp f ∘ s) ∘ p2 A N⟩ = (f ∘ ⟨p1 A N,s ∘ p2 A N⟩)’
     suffices_by
       (strip_tac >> simp[EQ_SYM_EQ] >> irule is_tp >>
        qexistsl_tac [‘A’,‘B’,‘N’] >> rw[]) >>
  ‘⟨p1 A N,(tp f ∘ s) ∘ p2 A N⟩ =
   ⟨p1 A N, (tp f) o (p2 A N)⟩ o ⟨p1 A N, s o (p2 A N)⟩’
    by cheat >>
  fs[] >>
  ‘ev A B ∘ ⟨p1 A N,tp f ∘ p2 A N⟩ = f’ by cheat >>
  cheat (*assoc of composition*)
   )
   



cheat >>
‘(h ∘ ⟨id (A×N),f⟩)∶ A×N → B ∧
 (f ∘ ⟨p1 A N,s ∘ p2 A N⟩)∶ A×N → B’ by cheat >>
metis_tac[tp_eq]
QED        


Theorem Thm1_comm_eq_condition:
∀A B f g h. g∶ A → B ∧ h∶ (po (po A N) B) → B ∧ f∶ po A N → B ⇒
       ((f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one) ∧
        h o ⟨id (po A N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩) ⇔
        (tp f o z = tp (g o (p1 A one)) ∧
        tp (h o ⟨
                 ⟨p1 A (po N (exp A B)),
                  (p1 N (exp A B)) o p2 A (po N (exp A B))
                 ⟩,
                 (ev A B) o
                 ⟨p1 A (po N (exp A B)), (p2 N (exp A B)) o p2 A (po N (exp A B))⟩⟩) o
         ⟨id N, tp f⟩ = (tp f) o s))
Proof
metis_tac[Thm1_comm_eq_left,Thm1_comm_eq_right]
QED        
        
Theorem Thm_1:
∀g h A B. g∶ A → B ∧ h∶ (po (po A N) B) → B ⇒
          ∃!f. f∶ po A N → B ∧
               f o ⟨p1 A one, z o (p2 A one)⟩ = g o (p1 A one) ∧
               h o ⟨id (po A N), f⟩ = f o ⟨p1 A N, s o (p2 A N)⟩
Proof
rw[] >>
qabbrev_tac ‘g' = tp (g o (p1 A one))’ >>
qabbrev_tac ‘h' = tp (h o
                      ⟨⟨p1 A (po N (exp A B)), (p1 N (exp A B)) o p2 A (po N (exp A B))⟩,
                      (ev A B) o
                      ⟨p1 A (po N (exp A B)), (p2 N (exp A B)) o p2 A (po N (exp A B))⟩⟩)’>>
‘g'∶ one → exp A B’ by cheat >>                                                            ‘h'∶ po N (exp A B) → exp A B’ by cheat >>
drule_all Thm1_case_1 >> strip_tac >>
fs[Once EXISTS_UNIQUE_ALT] >>
qexists_tac ‘(ev A B) o ⟨p1 A N, f o (p2 A N)⟩’ >>
‘f∶N → exp A B’ by metis_tac[] >>
rename [‘fb∶ N → exp A B’] >>
qabbrev_tac ‘f = ev A B ∘ ⟨p1 A N,fb ∘ p2 A N⟩’ >>
‘f∶A×N → B’ by cheat >>
simp[EQ_IMP_THM] >> strip_tac >> strip_tac (* 2 *)
>- rw[] >>
   ‘ tp f' ∘ z = tp (g ∘ p1 A one) ∧
          tp
            (h ∘
             ⟨⟨p1 A (N×exp A B),p1 N (exp A B) ∘ p2 A (N×exp A B)⟩,ev A B ∘
             ⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩⟩) ∘
          ⟨id N,tp f'⟩ =
          tp f' ∘ s’ by metis_tac[Thm1_comm_eq_condition] >>
    ‘tp f' = fb’ by cheat >>
    ‘tp f = fb’ by cheat >>
    (*tp eq implies original eq*) >>
    metis_tac[tp_eq]
>- strip_tac >>
   ‘tp f' ∘ z = tp (g ∘ p1 A one) ∧
          tp
            (h ∘
             ⟨⟨p1 A (N×exp A B),p1 N (exp A B) ∘ p2 A (N×exp A B)⟩,ev A B ∘
             ⟨p1 A (N×exp A B),p2 N (exp A B) ∘ p2 A (N×exp A B)⟩⟩) ∘
          ⟨id N,tp f'⟩ =
          tp f' ∘ s’ suffices_by metis_tac[Thm1_comm_eq_condition] >>
    fs[] >>
    ‘tp f = fb’ by cheat >> metis_tac[]
QED    
(*outlined*)
