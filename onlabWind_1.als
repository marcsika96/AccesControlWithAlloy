abstract sig Module extends EObject{
	provides: set Signal,
	consumes: set Signal
}

sig Composit extends Module{
	submodules: set Module,
	protectedIP: one ProtectedIP	
}

sig Control extends Module{
	type: one ControlUnitType,
	cycle: one Cycle
}

abstract sig EObject{}

sig Signal extends EObject{}

abstract sig ProtectedIP {}
one sig True, False extends ProtectedIP {}

abstract sig Cycle {}
one sig Low, Medium, High extends Cycle {}

abstract sig ControlUnitType {}
one sig FanCtrl, HeaterCtrl, PumpCtrl extends ControlUnitType {}


----------------------------------------------------------------------------------

abstract sig Specialist{
	modifiable: set EObject,
	visible: set EObject,
    responsibility : one Composit
}

sig  FanSpecialist, HeaterSpecialist, PumpSpecialist extends Specialist {}



//constraints

fact{
	all spec : Specialist{
		all comp : Composit{
			comp not in spec.responsibility implies comp.submodules not in spec.modifiable
		}
	}
}

//modifiability constraint
fact {
	all o: EObject, s: Specialist {
		(s->o in modifiable)
			<=>
		(some control : Control {
			(control in s.responsibility.^submodules) 
				and
			(o = control or o in control.provides)
				and
			((control.type=FanCtrl and s in FanSpecialist)
				or
			 (control.type=PumpCtrl and s in PumpSpecialist)
				or
		   	 (control.type=HeaterCtrl and s in HeaterSpecialist))
		})
	}
}

//visiblity constraint
fact{
	all s: Specialist, o : EObject{
			(s->o in visible)    
				<=> 
			(s.responsibility.protectedIP in False)
				and			
			((o in s.responsibility)
			    or 
			(o in s.responsibility.^submodules)
			    or 
			(o in s.responsibility.provides)
		   	    or 
			(o in s.responsibility.^submodules.provides))

}
}


//other constraints
--egy modul providol minden signalt
fact{
	all signal : Signal { one myModule : Module | signal in myModule.provides }
}

--minden kontrol egy kompozit submodulja
fact {
	all control : Control { one composit : Composit | control in composit.submodules }
}

-- minden kontorolnak pontosan egy őse van csak egy kopozit submodulja
fact {
	all m: Module, c1,c2: Composit {m in c1.submodules and m in c2.submodules implies c1 = c2 }
}

--egy sugnal csak akkor providolhat és fogyaszthat két mudul ha ugyanaz az ősük
fact{
	all mod1, mod2 : Module{
		all signal : Signal {
			(signal in mod1.provides and signal in mod2.consumes) implies 
				mod1.~submodules = mod2.~submodules
		}
	} 
}

--egy kontol valakinek a submodulja akkor valaki másnak már nem lehet a submodulja
fact{
	all comp1, comp2 : Composit{
		all control : Control |
			(control in comp1.submodules  and comp1 != comp2)implies
				control not in comp2.submodules
		
	}
}

--senki nem lehet önmaga submoduljai között
fact{
	no mod : Module | mod in mod.^submodules 
}

/*
//visible part
one sig o2 extends Composit{}
one sig o7 ,o10 extends Control{}
one sig o3, o4, o5, o6, o8, o9, o11, o12 extends Signal{} 
one sig fanSpec extends FanSpecialist{}

fact{
		 o10 in o2.submodules and
		 o10.cycle = High and
		 o7 in o2.submodules and
	     o7.cycle = High and
		 o3 in o2.provides and
		 o4 in o2.provides and
		 o5 in o2.provides and
		 o6 in o2.provides and
		 o8 in o7.provides and
		 o9 in o7.provides and
		 o11 in o10.provides and
		 o12 in o10.provides and
		 o11 in o7.consumes and
		 o12 in o7.consumes and
		 o8 in o10.consumes and
		 o9 in o10.consumes and
		
		 o2.protectedIP = False and
		 o10.type = FanCtrl and
		 o7.type=PumpCtrl and 
		 o10 in fanSpec.modifiable   
}


fact{
		fanSpec.visible = (o2 + o3 + o4 + o5 + o6 + o7 + o8 + o9 + o10 + o11 + o12)
}
*/


//fact {some s1, s2: Specialist {s1.visible != s2.visible and s1.visible in s2.visible and s1.visible != none}}
/*run {}
for  exactly 0 EObject,
	exactly 5 Control,
			exactly 2 Composit,
			exactly 5 Signal,
			exactly 0 Specialist*/

run {} for exactly 12 EObject,exactly 4 Control, exactly 6 Signal, exactly 3 Specialist

/*
run {} for  exactly 0 EObject,exactly 0 Specialist
run {} for  exactly 1 EObject,exactly 0 Specialist
run {} for  exactly 2 EObject,exactly 0 Specialist
run {} for  exactly 3 EObject,exactly 0 Specialist
run {} for  exactly 4 EObject,exactly 0 Specialist
run {} for  exactly 5 EObject,exactly 0 Specialist

run {} for  exactly 6 EObject,exactly 0 Specialist
run {} for  exactly 7 EObject,exactly 0 Specialist
run {} for  exactly 8 EObject,exactly 0 Specialist
run {} for  exactly 9 EObject,exactly 0 Specialist
run {} for  exactly 10 EObject,exactly 0 Specialist
run {} for  exactly 11 EObject,exactly 0 Specialist
run {} for  exactly 12 EObject,exactly 0 Specialist
run {} for  exactly 13 EObject,exactly 0 Specialist
run {} for  exactly 14 EObject,exactly 0 Specialist
run {} for  exactly 15 EObject,exactly 0 Specialist
run {} for  exactly 16 EObject,exactly 0 Specialist
run {} for  exactly 17 EObject,exactly 0 Specialist
run {} for  exactly 18 EObject,exactly 0 Specialist
run {} for  exactly 19 EObject,exactly 0 Specialist
*/
//run {} for  exactly 20 EObject,exactly 0 Specialist
/*
run {} for  exactly 21 EObject,exactly 0 Specialist
run {} for  exactly 22 EObject,exactly 0 Specialist
run {} for  exactly 23 EObject,exactly 0 Specialist
run {} for  exactly 24 EObject,exactly 0 Specialist
run {} for  exactly 25 EObject,exactly 0 Specialist
run {} for  exactly 26 EObject,exactly 0 Specialist
run {} for  exactly 27 EObject,exactly 0 Specialist
run {} for  exactly 28 EObject,exactly 0 Specialist
run {} for  exactly 29 EObject,exactly 0 Specialist
run {} for  exactly 30 EObject,exactly 0 Specialist
run {} for  exactly 31 EObject,exactly 0 Specialist
run {} for  exactly 32 EObject,exactly 0 Specialist
run {} for  exactly 33 EObject,exactly 0 Specialist
run {} for  exactly 34 EObject,exactly 0 Specialist
run {} for  exactly 35 EObject,exactly 0 Specialist
run {} for  exactly 36 EObject,exactly 0 Specialist
run {} for  exactly 37 EObject,exactly 0 Specialist
run {} for  exactly 38 EObject,exactly 0 Specialist
run {} for  exactly 39 EObject,exactly 0 Specialist
run {} for  exactly 40 EObject,exactly 0 Specialist
run {} for  exactly 41 EObject,exactly 0 Specialist
run {} for  exactly 42 EObject,exactly 0 Specialist
run {} for  exactly 43 EObject,exactly 0 Specialist
run {} for  exactly 44 EObject,exactly 0 Specialist
run {} for  exactly 45 EObject,exactly 0 Specialist
run {} for  exactly 46 EObject,exactly 0 Specialist
run {} for  exactly 47 EObject,exactly 0 Specialist
run {} for  exactly 48 EObject,exactly 0 Specialist
run {} for  exactly 49 EObject,exactly 0 Specialist
run {} for  exactly 50 EObject,exactly 0 Specialist
*/
