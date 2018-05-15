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

//one sig SupremeLeader extends Specialist {}

//constraints

fact{
	all spec : Specialist{
		all comp : Composit{
			comp not in spec.responsibility implies comp.submodules not in spec.modifiable
		}
	}
}
/*
//facSpecialist constraints

fact{
	all fanSpec : FanSpecialist | fanSpec.modifiable.type in FanCtrl
}

fact{
	all fanSpec : FanSpecialist | fanSpec.modifiable in fanSpec.modifiable.provides
}

fact{
	all fanSpec : FanSpecialist | fanSpec.modifiable.provides  in fanSpec.modifiable
}

//heaterSpesialist contraints
fact{
	all heatSpec : HeaterSpecialist | heatSpec.modifiable.type in HeaterCtrl
}

fact{
	all heatSpec : HeaterSpecialist | heatSpec.modifiable in heatSpec.modifiable.provides
}

fact{
	all heatSpec : HeaterSpecialist | heatSpec.modifiable.provides in heatSpec.modifiable
}

//pumpSpecialist constraints
fact{
	all pumpSpec : PumpSpecialist | pumpSpec.modifiable.type in PumpCtrl
}

fact{
	all pumpSpec : PumpSpecialist | pumpSpec.modifiable in pumpSpec.modifiable.provides
}

fact{
	all pumpSpec : PumpSpecialist | pumpSpec.modifiable.provides in pumpSpec.modifiable
}
*/

/*
//supremeLeader constraints
fact{
	all control : Control , supremeLeader : SupremeLeader | control in supremeLeader.modifiable
}

fact{
	all control : Control , supremeLeader : SupremeLeader | control in supremeLeader.visible
}

fact {
	all signal : Signal, supremeLeader : SupremeLeader | signal in supremeLeader.modifiable
}

fact {
	all signal : Signal, supremeLeader : SupremeLeader | signal in supremeLeader.visible
}
*/
//modifiablity constraint
/*
fact{
	all spec: Specialist{
		all o : EObject{
			(spec->o in modifiable) <=> (( o in Control and 
										( (o.type=FanCtrl and spec in FanSpecialist) or
										  (o.type=PumpCtrl and spec in PumpSpecialist) or
									   	  (o.type=HeaterCtrl and spec in HeaterSpecialist) ) and
										   o in spec.responsibility.submodules)) or
									 ( o in Signal and o in spec.modifiable.provides ) 
}
}
}*/

/*
fact{
	all o : EObject{
		all spec : Specialist{
			(o in Signal and o in spec.modifiable.provides) iff ((o.~provides in spec.modifiable) and 
																(o.~provides.type=FanCtrl and spec in FanSpecialist) or
										  						(o.~provides.type=PumpCtrl and spec in PumpSpecialist) or
									   	  						(o.~provides.type=HeaterCtrl and spec in HeaterSpecialist)) and
																o in spec.modifiable
}
}
}*/

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
fact{
	all signal : Signal { one myModule : Module | signal in myModule.provides }
}

fact {
	all control : Control { one composit : Composit | control in composit.submodules }
}

fact {
	all m: Module, c1,c2: Composit {m in c1.submodules and m in c2.submodules implies c1 = c2 }
}

/*

//még nem jó
//minden specialist látja azokat a control - okat amelyek az általa szerkeszthető control-okkal egy
//compositban vannak és a comopsit nem védett.
//minden specialist látja azokat a signal - okat amelyek az általa szerkeszthető control-okkal 
//egy compositban levő controlok illetve a composit által vannak providolva és a comopsit nem
//védett.
// Control látható ha -- constraint

fact{ 
	all spec : Specialist{
				all control : Control | ( control.~submodules.protectedIP=False 
								and control in spec.modifiable ) implies
								control.~submodules.submodules in spec.visible
	}
}

//egy control csak akkor látható egy specialist számára ha az általa szerkezthető conrtolok egy 
//compositban vannak vele, és a composit nem védett
fact{
	all control : Control {
		all spec : Specialist |  control in spec.visible implies
								spec.modifiable in control.~submodules.submodules
	}
}

fact{
	all spec : Specialist {
		all control : Control | control not in spec.visible 
								or control.provides in spec.visible
	}
}


fact{
	all spec : Specialist {
		all comp : Composit | spec.modifiable not in comp.submodules
							  or comp.provides in spec.visible 
	}
}
*/

fact{
	all mod1, mod2 : Module{
		all signal : Signal {
			(signal in mod1.provides and signal in mod2.consumes) implies 
				mod1.~submodules = mod2.~submodules
		}
	} 
}

fact{
	all comp1, comp2 : Composit{
		all control : Control |
			(control in comp1.submodules  and comp1 != comp2)implies
				control not in comp2.submodules
		
	}
}

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
run {} for exactly 15 EObject,exactly 5 Control, exactly 5 Signal, 0 Specialist
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
run {} for  exactly 20 EObject,exactly 0 Specialist
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
