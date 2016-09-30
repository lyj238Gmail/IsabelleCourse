theory flash imports flashMainLemma
begin

lemma main:
  assumes   a1:"s \<in> reachableSet {andList (allIniSpecs   N)} (rules N)"  and a2:"0<N"

  shows "\<forall>invf. invf \<in>(invariants N)\<longrightarrow>formEval invf s"
proof(rule newconsistentLemma)
  show "newconsistent (invariants N) {andList (allIniSpecs   N)}(rules N)"
  proof(cut_tac a1, unfold newconsistent_def,rule conjI)
    show " \<forall>invf ini s. invf \<in>(invariants N)\<longrightarrow> ini \<in>{andList (allIniSpecs   N)}\<longrightarrow> formEval ini s\<longrightarrow> formEval invf s"
    proof((rule allI)+,(rule impI)+)
      fix invf ini s 
      assume b1:"invf \<in>(invariants N) " and b2:"ini \<in> {andList (allIniSpecs   N)} " and b3:"formEval ini s"
                
      have b4:"formEval (andList (allIniSpecs   N)) s"
         by(cut_tac b2 b3,simp)

      show "formEval invf s"
      proof -     
        
        have c1:" ex2P N (% iInv1  iInv2 .  invf= inv1  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv2  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv3  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv4  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv5  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv6  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv7  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv8  iInv1  iInv2 )  \<or> ex1P N (% iInv1 .  invf= inv9  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv10  iInv1 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv11  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv12 )  \<or> ex1P N (% iInv1 .  invf= inv13  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv14  iInv1 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv15  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv16  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv17  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv18  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv19  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv20  iInv1  iInv2 )  \<or> ex1P N (% iInv1 .  invf= inv21  iInv1 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv22  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv23  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv24  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv25  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv26  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv27  iInv1  iInv2 )  \<or> ex1P N (% iInv1 .  invf= inv28  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv29  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv30  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv31  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv32  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv33  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv34  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv35  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv36  iInv1 )  \<or> ex0P N  (  invf= inv37 )  \<or> ex0P N  (  invf= inv38 )  \<or> ex0P N  (  invf= inv39 )  \<or> ex1P N (% iInv1 .  invf= inv40  iInv1 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv41  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv42  iInv1  iInv2  iInv3 )  \<or> ex0P N  (  invf= inv43 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv44  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv45 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv46  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv47 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv48  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv49  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv50  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv51  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv52  iInv1  iInv2  iInv3 )  \<or> ex0P N  (  invf= inv53 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv54  iInv1  iInv2  iInv3 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv55  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv56  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv57  iInv1  iInv2 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv58  iInv1  iInv2  iInv3 )  \<or> ex3P N (% iInv1  iInv2  iInv3 .  invf= inv59  iInv1  iInv2  iInv3 )  \<or> ex1P N (% iInv1 .  invf= inv60  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv61  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv62  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv63  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv64  iInv1 )  \<or> ex1P N (% iInv1 .  invf= inv65  iInv1 )  \<or> ex0P N  (  invf= inv66 )  \<or> ex0P N  (  invf= inv67 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv68  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv69  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv70  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv71 )  \<or> ex0P N  (  invf= inv72 )  \<or> ex0P N  (  invf= inv73 )  \<or> ex0P N  (  invf= inv74 )  \<or> ex0P N  (  invf= inv75 )  \<or> ex0P N  (  invf= inv76 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv77  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv78 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv79  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv80 )  \<or> ex0P N  (  invf= inv81 )  \<or> ex1P N (% iInv1 .  invf= inv82  iInv1 )  \<or> ex0P N  (  invf= inv83 )  \<or> ex0P N  (  invf= inv84 )  \<or> ex0P N  (  invf= inv85 )  \<or> ex0P N  (  invf= inv86 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv87  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv88  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv89  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv90  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv91 )  \<or> ex0P N  (  invf= inv92 )  \<or> ex0P N  (  invf= inv93 )  \<or> ex0P N  (  invf= inv94 )  \<or> ex0P N  (  invf= inv95 )  \<or> ex0P N  (  invf= inv96 )  \<or> ex0P N  (  invf= inv97 )  \<or> ex0P N  (  invf= inv98 )  \<or> ex0P N  (  invf= inv99 )  \<or> ex0P N  (  invf= inv100 )  \<or> ex1P N (% iInv1 .  invf= inv101  iInv1 )  \<or> ex0P N  (  invf= inv102 )  \<or> ex0P N  (  invf= inv103 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv104  iInv1  iInv2 )  \<or> ex2P N (% iInv1  iInv2 .  invf= inv105  iInv1  iInv2 )  \<or> ex0P N  (  invf= inv106 )  \<or> ex0P N  (  invf= inv107 )  \<or> ex0P N  (  invf= inv108 )  \<or> ex0P N  (  invf= inv109 )  \<or> ex0P N  (  invf= inv110 )  \<or> ex0P N  (  invf= inv111 )  \<or> ex0P N  (  invf= inv112 )  \<or> ex0P N  (  invf= inv113 )   "
          by (cut_tac b1, simp )       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv1  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv1.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv2  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv2.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv3  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv3.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv4  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv4.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv5  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv5.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv6  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv6.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv7  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv7.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv8  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv8.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv9  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv9.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv10  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv10.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv11  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv11.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv12 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv12.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv13  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv13.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv14  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv14.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv15  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv15.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv16  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv16.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv17  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv17.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv18  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv18.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv19  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv19.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv20  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv20.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv21  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv21.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv22  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv22.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv23  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv23.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv24  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv24.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv25  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv25.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv26  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv26.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv27  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv27.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv28  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv28.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv29  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv29.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv30  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv30.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv31  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv31.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv32  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv32.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv33  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv33.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv34  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv34.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv35  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv35.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv36  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv36.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv37 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv37.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv38 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv38.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv39 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv39.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv40  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv40.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv41  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv41.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv42  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv42.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv43 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv43.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv44  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv44.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv45 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv45.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv46  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv46.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv47 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv47.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv48  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv48.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv49  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv49.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv50  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv50.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv51  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv51.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv52  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv52.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv53 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv53.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv54  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv54.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv55  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv55.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv56  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv56.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv57  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv57.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv58  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv58.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex3P N (% iInv1  iInv2  iInv3 .  invf= inv59  iInv1  iInv2  iInv3 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv59.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv60  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv60.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv61  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv61.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv62  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv62.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv63  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv63.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv64  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv64.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv65  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv65.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv66 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv66.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv67 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv67.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv68  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv68.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv69  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv69.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv70  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv70.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv71 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv71.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv72 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv72.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv73 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv73.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv74 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv74.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv75 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv75.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv76 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv76.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv77  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv77.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv78 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv78.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv79  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv79.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv80 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv80.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv81 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv81.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv82  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv82.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv83 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv83.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv84 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv84.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv85 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv85.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv86 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv86.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv87  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv87.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv88  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv88.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv89  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv89.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv90  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv90.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv91 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv91.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv92 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv92.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv93 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv93.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv94 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv94.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv95 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv95.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv96 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv96.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv97 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv97.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv98 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv98.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv99 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv99.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv100 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv100.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex1P N (% iInv1 .  invf= inv101  iInv1 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv101.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv102 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv102.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv103 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv103.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv104  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv104.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex2P N (% iInv1  iInv2 .  invf= inv105  iInv1  iInv2 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv105.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv106 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv106.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv107 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv107.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv108 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv108.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv109 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv109.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv110 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv110.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv111 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv111.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv112 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv112.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }
       moreover
        {assume d1: " ex0P N  (  invf= inv113 )  "

          have "formEval invf s"

            by(metis b4 d1 iniImply_inv113.iniImplyInv)
           (* apply(cut_tac d1,assumption)
           by (cut_tac  b4,simp)*)
        }

      ultimately show "formEval invf s"
      by blast
      qed
    qed
next
   show  "\<forall>invf r s. invf \<in> invariants N\<longrightarrow> r \<in>rules N\<longrightarrow> invHoldForRule' s invf r (invariants N) "
   

   proof((rule allI)+,(rule impI)+)
      fix invf r s
      assume b1:"invf \<in> invariants N" and b2:"r \<in> rules N"
      show "invHoldForRule' s invf r (invariants N) "
          by (metis mainLemma b1 b2) 
     qed
qed
next
  show "s \<in> reachableSet {andList (allIniSpecs   N)}  (rules N)"
by (metis a1)
 
 
qed
end  
