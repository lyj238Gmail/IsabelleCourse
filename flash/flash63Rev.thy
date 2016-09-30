theory flash63Rev imports flashPub
begin
section{*Main defintions*}
lemma NI_FAckVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_FAck ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_InvVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Inv  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_InvAck_1VsInv63:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_InvAck_1  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have "?P2 s" 

     by(cut_tac a1 a2 a3 a4, auto) 
   then show "?P1 s\<or>?P2 s\<or>?P3 s"
      by auto 
 qed
  lemma NI_InvAck_1_HomeVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_InvAck_1_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_InvAck_2VsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_InvAck_2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_GetX_GetXVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak1VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak2VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_Nak3VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX1VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX2VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX2 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX3VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX3 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX4VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX4 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX5VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX5 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX6VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX6 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX7VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX7 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8VsInv63:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX8 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX8_homeVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX8_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX9VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX9 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10VsInv63:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX10 N  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX10_homeVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX10_home N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))    ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_GetX_PutX11VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_GetX_PutX11 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_GetVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Get_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Local_Get_Nak1VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak2VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Get_Nak2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Nak3VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Get_Nak3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put1VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Get_Put1 N  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put2VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Get_Put2  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_Get_Put3VsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Get_Put3  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_PutVsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

     have allCases:"formEval  ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  s  \<or>formEval   (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  s  "  
	                      by auto 

    moreover
                       {assume b1:"formEval ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  s"

      have "?P1 s"
         
        apply(cut_tac  a1  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  s"

      have "?P1 s"
         
        apply(cut_tac  a1  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Local_PutXAcksDoneVsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Local_PutXAcksDone ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' Home) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma NI_NakVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Nak  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Nak_ClearVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Nak_Clear ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_Nak_HomeVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Nak_Home ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_Remote_GetX_NakVsInv63:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_GetX_Nak  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_Nak_HomeVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_GetX_Nak_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Remote_GetX_PutXVsInv63:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_GetX_PutX  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  
      have "?P3 s"

         
        apply(   cut_tac  a1  a2  a3  a4  b1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''CacheState'' iRule2) )  ( Const CACHE_E ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_E ))  ) ) " in exI,auto)
 
        
        done

       
       then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_GetX_PutX_HomeVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_GetX_PutX_Home  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Remote_Get_Nak1VsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_Get_Nak1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Remote_Get_Nak2VsInv63:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_Get_Nak2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_Get_Put1VsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_Get_Put1  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_Remote_Get_Put2VsInv63:  
    (*Rule2VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iRule2 \<le> N" and  a3:"iInv1 \<le> N" and  a4:"iRule1~=iRule2  " 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_Get_Put2  iRule1  iRule2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))   \<or>((iRule1~=iInv1 )\<and>iRule2=iInv1)   \<or>((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  a3  a4  , auto) 
moreover
                {assume b1:"(iRule1=iInv1\<and>(iRule2~=iInv1 ))"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  a3  a4  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>iRule2=iInv1)"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 )\<and>(iRule2~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  a3  a4  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_Put  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_Remote_PutXVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma NI_ReplaceVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_ReplaceHomeVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_ReplaceHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_ReplaceHomeShrVldVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_ReplaceHomeShrVld ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_ReplaceShrVldVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_ReplaceShrVld  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma NI_ShWbVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_ShWb N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma NI_WbVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (NI_Wb ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_GetX_GetX1VsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_GetX_GetX1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_GetX_GetX2VsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_GetX_GetX2 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_GetX_PutX1VsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_GetX_PutX1 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma PI_Local_GetX_PutX2VsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_GetX_PutX2 N ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma PI_Local_GetX_PutX3VsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_GetX_PutX3 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Global ''Dir_Dirty'') )  ( Const false ))    ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma PI_Local_GetX_PutX4VsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_GetX_PutX4 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P3 s"

         
        apply(   cut_tac  a1 , simp)

        apply(rule_tac x=" (neg ( andForm ( eqn ( IVar ( Para ''UniMsg_Cmd'' iInv1) )  ( Const UNI_PutX ))    ( eqn ( IVar ( Para ''CacheState'' Home) )  ( Const CACHE_S ))  ) ) " in exI,auto)
 
        
        done

       
       then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

        by blast

  


 qed
lemma PI_Local_Get_GetVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_Get_Get ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 lemma PI_Local_Get_PutVsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_Get_Put ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

     have allCases:"formEval  ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  s  \<or>formEval   (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  s  "  
	                      by auto 

    moreover
                       {assume b1:"formEval ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true ))  s"

      have "?P1 s"
         
        apply(cut_tac  a1  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }

    moreover
                       {assume b1:"formEval  (neg ( eqn ( IVar ( Para ''InvMarked'' Home) )  ( Const true )) )  s"

      have "?P1 s"
         
        apply(cut_tac  a1  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast
    }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Local_PutXVsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_PutX ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Local_ReplaceVsInv63:  
  (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Local_Replace ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 

  
      have "?P1 s"
         
        apply(cut_tac  a1 , auto)

         
        done

        then  show "?P1 s\<or> ?P2 s\<or> ?P3 s"

       by blast

  


 qed
lemma PI_Remote_GetVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Remote_Get  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_GetXVsInv63:  
  (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Remote_GetX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

  proof - 
 

     have allCases:"(iRule1=iInv1)   \<or>((iRule1~=iInv1 ))   "  
	                      by( cut_tac  a1  a2  , auto) 
moreover
                {assume b1:"(iRule1=iInv1)"

                  
      have "?P1 s"
         
        apply(cut_tac  a1  a2  b1 , auto)

         
        done

        then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

       by blast

  

	                }
moreover
                {assume b1:"((iRule1~=iInv1 ))"

                  have "?P2 s"

   
  apply(cut_tac  a1  a2  b1 , auto intro!:forallVars1 simp  add :invHoldForRule2'_def varsOfVar_def)
       
  done

  then  have "?P1 s\<or> ?P2 s \<or> ?P3 s"

        by blast

  

	                }
   ultimately show "?P1 s\<or> ?P2 s\<or> ?P3 s"

	                         by metis

                     


 qed
lemma PI_Remote_PutXVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Remote_PutX  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma PI_Remote_ReplaceVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (PI_Remote_Replace  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma StoreVsInv63:  
    (*Rule1VsPInv1*)
  assumes   a1:"iRule1 \<le> N" and  a2:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (Store  iRule1 ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by  (cut_tac  a1  a2 , auto)
 lemma StoreHomeVsInv63:  
    (*Rule0VsPInv1*)
  assumes   a1:"iInv1 \<le> N" 

  shows  "invHoldForRule' s (inv63  iInv1 ) (StoreHome ) (invariants   N)" (is " ?P1 s\<or>?P2 s\<or>?P3 s")  

    by (cut_tac  a1 , auto)
 end
