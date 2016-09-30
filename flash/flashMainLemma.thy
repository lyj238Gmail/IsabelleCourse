theory flashMainLemma imports   flash1Bra  flash2Bra  flash3Bra  flash4Bra  flash5Bra  flash6Bra  flash7Bra  flash8Bra  flash9Bra  flash10Bra  flash11Bra  flash12Bra  flash13Bra  flash14Bra  flash15Bra  flash16Bra  flash17Bra  flash18Bra  flash19Bra  flash20Bra  flash21Bra  flash22Bra  flash23Bra  flash24Bra  flash25Bra  flash26Bra  flash27Bra  flash28Bra  flash29Bra  flash30Bra  flash31Bra  flash32Bra  flash33Bra  flash34Bra  flash35Bra  flash36Bra  flash37Bra  flash38Bra  flash39Bra  flash40Bra  flash41Bra  flash42Bra  flash43Bra  flash44Bra  flash45Bra  flash46Bra  flash47Bra  flash48Bra  flash49Bra  flash50Bra  flash51Bra  flash52Bra  flash53Bra  flash54Bra  flash55Bra  flash56Bra  flash57Bra  flash58Bra  flash59Bra  flash60Bra  flash61Bra  flash62Bra  flash63Bra  flash64Bra  flash65Bra  flash66Bra  flash67Bra  flash68Bra  flash69Bra  flash70Bra  flash71Bra  flash72Bra  flash73Bra  flash74Bra  flash75Bra  flash76Bra  flash77Bra  flash78Bra  flash79Bra  flash80Bra  flash81Bra  flash82Bra  flash83Bra  flash84Bra  flash85Bra  flash86Bra  flash87Bra  flash88Bra  flash89Bra  flash90Bra  flash91Bra  flash92Bra  flash93Bra  flash94Bra  flash95Bra  flash96Bra  flash97Bra  flash98Bra  flash99Bra  flash100Bra  flash101Bra  flash102Bra  flash103Bra  flash104Bra  flash105Bra  flash106Bra  flash107Bra  flash108Bra  flash109Bra  flash110Bra  flash111Bra  flash112Bra  flash113Bra  
begin
lemma mainLemma:

   assumes   

     a1:"r \<in> rules N" and a2:"invf \<in> (invariants N)"
   shows  "invHoldForRule' s invf r (invariants   N)"

   proof -  
  have c1:" ex2P N (% iInv1  iInv2 .  invf= inv1  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv2  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv3  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv4  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv5  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv6  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv7  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv8  iInv1  iInv2 )  \<or> ex1P N (% iInv1 .  invf= inv9  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv10  iInv1 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv11  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv12 )  \<or> ex1P N (% iInv1 .  invf= inv13  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv14  iInv1 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv15  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv16  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv17  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv18  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv19  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv20  iInv1  iInv2 )  \<or> ex1P N (% iInv1 .  invf= inv21  iInv1 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv22  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv23  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv24  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv25  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv26  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv27  iInv1  iInv2 )  \<or> ex1P N (% iInv1 .  invf= inv28  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv29  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv30  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv31  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv32  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv33  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv34  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv35  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv36  iInv1 )  \<or> ex0P N  (  invf= inv37 )  \<or> ex0P N  (  invf= inv38 )  \<or> ex0P N  (  invf= inv39 )  \<or> ex1P N (% iInv1 .  invf= inv40  iInv1 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv41  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv42  iInv1  iInv2  iInv3 )  \<or> ex0P N  (  invf= inv43 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv44  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv45 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv46  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv47 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv48  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv49  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv50  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv51  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv52  iInv1  iInv2  iInv3 )  \<or> ex0P N  (  invf= inv53 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv54  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv55  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv56  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv57  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv58  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv59  iInv1  iInv2  iInv3 )  \<or> ex1P N (% iInv1 .  invf= inv60  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv61  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv62  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv63  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv64  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv65  iInv1 )  \<or> ex0P N  (  invf= inv66 )  \<or> ex0P N  (  invf= inv67 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv68  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv69  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv70  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv71 )  \<or> ex0P N  (  invf= inv72 )  \<or> ex0P N  (  invf= inv73 )  \<or> ex0P N  (  invf= inv74 )  \<or> ex0P N  (  invf= inv75 )  \<or> ex0P N  (  invf= inv76 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv77  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv78 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv79  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv80 )  \<or> ex0P N  (  invf= inv81 )  \<or> ex1P N (% iInv1 .  invf= inv82  iInv1 )  \<or> ex0P N  (  invf= inv83 )  \<or> ex0P N  (  invf= inv84 )  \<or> ex0P N  (  invf= inv85 )  \<or> ex0P N  (  invf= inv86 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv87  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv88  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv89  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv90  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv91 )  \<or> ex0P N  (  invf= inv92 )  \<or> ex0P N  (  invf= inv93 )  \<or> ex0P N  (  invf= inv94 )  \<or> ex0P N  (  invf= inv95 )  \<or> ex0P N  (  invf= inv96 )  \<or> ex0P N  (  invf= inv97 )  \<or> ex0P N  (  invf= inv98 )  \<or> ex0P N  (  invf= inv99 )  \<or> ex0P N  (  invf= inv100 )  \<or> ex1P N (% iInv1 .  invf= inv101  iInv1 )  \<or> ex0P N  (  invf= inv102 )  \<or> ex0P N  (  invf= inv103 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv104  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv105  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv106 )  \<or> ex0P N  (  invf= inv107 )  \<or> ex0P N  (  invf= inv108 )  \<or> ex0P N  (  invf= inv109 )  \<or> ex0P N  (  invf= inv110 )  \<or> ex0P N  (  invf= inv111 )  \<or> ex0P N  (  invf= inv112 )  \<or> ex0P N  (  invf= inv113 )  " 

        apply(cut_tac  a2)
        apply auto
        done      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv1  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv1  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv1  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv1 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv2  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv2  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv2  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv2 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv3  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv3  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv3  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv3 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv4  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv4  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv4  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv4 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv5  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv5  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv5  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv5 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv6  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv6  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv6  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv6 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv7  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv7  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv7  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv7 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv8  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv8  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv8  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv8 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv9  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv9  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv9  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv9 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv10  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv10  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv10  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv10 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv11  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv11  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv11  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv11 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv12)
"
         
         from c1 have c2:" invf= inv12" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv12  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv12 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv13  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv13  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv13  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv13 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv14  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv14  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv14  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv14 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv15  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv15  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv15  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv15 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv16  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv16  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv16  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv16 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv17  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv17  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv17  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv17 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv18  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv18  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv18  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv18 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv19  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv19  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv19  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv19 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv20  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv20  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv20  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv20 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv21  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv21  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv21  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv21 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv22  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv22  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv22  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv22 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv23  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv23  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv23  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv23 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv24  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv24  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv24  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv24 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv25  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv25  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv25  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv25 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv26  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv26  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv26  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv26 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv27  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv27  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv27  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv27 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv28  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv28  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv28  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv28 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv29  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv29  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv29  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv29 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv30  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv30  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv30  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv30 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv31  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv31  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv31  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv31 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv32  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv32  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv32  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv32 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv33  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv33  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv33  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv33 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv34  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv34  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv34  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv34 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv35  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv35  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv35  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv35 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv36  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv36  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv36  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv36 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv37)
"
         
         from c1 have c2:" invf= inv37" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv37  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv37 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv38)
"
         
         from c1 have c2:" invf= inv38" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv38  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv38 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv39)
"
         
         from c1 have c2:" invf= inv39" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv39  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv39 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv40  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv40  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv40  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv40 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv41  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv41  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv41  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv41 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv42  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv42  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv42  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv42 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv43)
"
         
         from c1 have c2:" invf= inv43" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv43  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv43 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv44  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv44  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv44  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv44 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv45)
"
         
         from c1 have c2:" invf= inv45" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv45  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv45 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv46  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv46  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv46  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv46 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv47)
"
         
         from c1 have c2:" invf= inv47" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv47  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv47 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv48  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv48  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv48  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv48 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv49  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv49  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv49  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv49 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv50  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv50  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv50  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv50 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv51  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv51  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv51  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv51 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv52  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv52  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv52  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv52 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv53)
"
         
         from c1 have c2:" invf= inv53" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv53  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv53 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv54  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv54  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv54  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv54 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv55  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv55  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv55  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv55 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv56  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv56  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv56  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv56 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv57  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv57  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv57  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv57 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv58  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv58  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv58  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv58 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex3P N (% iInv1  iInv2  iInv3 .  invf= inv59  iInv1  iInv2  iInv3 )
"
         
         from c1 obtain  iInv1  iInv2  iInv3  where c2:"  iInv1~=iInv2    \<and>    iInv1~=iInv3    \<and>    iInv2~=iInv3    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>   iInv3 \<le> N \<and>  invf= inv59  iInv1  iInv2  iInv3 " 
         by (auto simp add: ex3P_def)
         
         have "invHoldForRule' s (inv59  iInv1  iInv2  iInv3 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv59 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv60  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv60  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv60  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv60 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv61  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv61  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv61  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv61 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv62  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv62  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv62  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv62 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv63  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv63  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv63  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv63 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv64  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv64  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv64  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv64 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv65  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv65  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv65  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv65 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv66)
"
         
         from c1 have c2:" invf= inv66" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv66  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv66 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv67)
"
         
         from c1 have c2:" invf= inv67" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv67  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv67 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv68  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv68  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv68  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv68 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv69  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv69  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv69  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv69 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv70  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv70  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv70  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv70 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv71)
"
         
         from c1 have c2:" invf= inv71" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv71  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv71 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv72)
"
         
         from c1 have c2:" invf= inv72" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv72  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv72 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv73)
"
         
         from c1 have c2:" invf= inv73" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv73  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv73 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv74)
"
         
         from c1 have c2:" invf= inv74" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv74  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv74 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv75)
"
         
         from c1 have c2:" invf= inv75" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv75  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv75 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv76)
"
         
         from c1 have c2:" invf= inv76" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv76  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv76 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv77  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv77  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv77  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv77 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv78)
"
         
         from c1 have c2:" invf= inv78" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv78  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv78 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv79  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv79  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv79  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv79 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv80)
"
         
         from c1 have c2:" invf= inv80" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv80  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv80 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv81)
"
         
         from c1 have c2:" invf= inv81" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv81  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv81 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv82  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv82  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv82  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv82 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv83)
"
         
         from c1 have c2:" invf= inv83" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv83  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv83 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv84)
"
         
         from c1 have c2:" invf= inv84" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv84  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv84 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv85)
"
         
         from c1 have c2:" invf= inv85" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv85  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv85 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv86)
"
         
         from c1 have c2:" invf= inv86" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv86  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv86 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv87  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv87  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv87  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv87 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv88  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv88  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv88  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv88 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv89  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv89  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv89  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv89 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv90  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv90  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv90  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv90 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv91)
"
         
         from c1 have c2:" invf= inv91" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv91  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv91 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv92)
"
         
         from c1 have c2:" invf= inv92" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv92  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv92 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv93)
"
         
         from c1 have c2:" invf= inv93" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv93  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv93 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv94)
"
         
         from c1 have c2:" invf= inv94" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv94  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv94 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv95)
"
         
         from c1 have c2:" invf= inv95" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv95  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv95 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv96)
"
         
         from c1 have c2:" invf= inv96" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv96  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv96 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv97)
"
         
         from c1 have c2:" invf= inv97" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv97  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv97 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv98)
"
         
         from c1 have c2:" invf= inv98" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv98  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv98 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv99)
"
         
         from c1 have c2:" invf= inv99" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv99  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv99 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv100)
"
         
         from c1 have c2:" invf= inv100" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv100  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv100 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex1P N (% iInv1 .  invf= inv101  iInv1 )
"
         
         from c1 obtain  iInv1  where c2:"  iInv1 \<le> N \<and>  invf= inv101  iInv1 " 
         by (auto simp add: ex1P_def)
         
         have "invHoldForRule' s (inv101  iInv1 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv101 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv102)
"
         
         from c1 have c2:" invf= inv102" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv102  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv102 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv103)
"
         
         from c1 have c2:" invf= inv103" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv103  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv103 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv104  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv104  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv104  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv104 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex2P N (% iInv1  iInv2 .  invf= inv105  iInv1  iInv2 )
"
         
         from c1 obtain  iInv1  iInv2  where c2:"  iInv1~=iInv2    \<and>    iInv1 \<le> N \<and>   iInv2 \<le> N \<and>  invf= inv105  iInv1  iInv2 " 
         by (auto simp add: ex2P_def)
         
         have "invHoldForRule' s (inv105  iInv1  iInv2 ) r (invariants N) "
            apply(cut_tac a1  c2   )
            by (metis onInv105 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2 , metis) 
        }      moreover
        {assume c1: "ex0P N (  invf= inv106)
"
         
         from c1 have c2:" invf= inv106" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv106  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv106 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv107)
"
         
         from c1 have c2:" invf= inv107" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv107  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv107 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv108)
"
         
         from c1 have c2:" invf= inv108" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv108  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv108 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv109)
"
         
         from c1 have c2:" invf= inv109" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv109  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv109 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv110)
"
         
         from c1 have c2:" invf= inv110" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv110  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv110 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv111)
"
         
         from c1 have c2:" invf= inv111" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv111  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv111 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv112)
"
         
         from c1 have c2:" invf= inv112" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv112  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv112 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}      moreover
        {assume c1: "ex0P N (  invf= inv113)
"
         
         from c1 have c2:" invf= inv113" 
         by (auto simp add: ex0P_def)
         
         have "invHoldForRule' s (inv113  ) r (invariants N) "
            apply(cut_tac  a1   c2 )
            by (metis onInv113 ) 
          then have "invHoldForRule' s invf r (invariants N) "
            by(cut_tac c2, metis) 
	}ultimately show "invHoldForRule' s invf r (invariants N) "
          by blast 
     qed
end
