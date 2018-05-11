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
	modifiable_control: set Control,
	visible_control: set Control,
	modifiable_signal: set Signal, 
	visible_signal: set Signal
}

sig  FanSpecialist, HeaterSpecialist, PumpSpecialist extends Specialist {}

//one sig SupremeLeader extends Specialist {}

//constraints

//facSpecialist constraints

fact{
	all fanSpec : FanSpecialist | fanSpec.modifiable_control.type in FanCtrl
}

fact{
	all fanSpec : FanSpecialist | fanSpec.modifiable_signal in fanSpec.modifiable_control.provides
}

fact{
	all fanSpec : FanSpecialist | fanSpec.modifiable_control.provides  in fanSpec.modifiable_signal
}

//heaterSpesialist contraints
fact{
	all heatSpec : HeaterSpecialist | heatSpec.modifiable_control.type in HeaterCtrl
}

fact{
	all heatSpec : HeaterSpecialist | heatSpec.modifiable_signal in heatSpec.modifiable_control.provides
}

fact{
	all heatSpec : HeaterSpecialist | heatSpec.modifiable_control.provides in heatSpec.modifiable_signal
}

//pumpSpecialist constraints
fact{
	all pumpSpec : PumpSpecialist | pumpSpec.modifiable_control.type in PumpCtrl
}

fact{
	all pumpSpec : PumpSpecialist | pumpSpec.modifiable_signal in pumpSpec.modifiable_control.provides
}

fact{
	all pumpSpec : PumpSpecialist | pumpSpec.modifiable_control.provides in pumpSpec.modifiable_signal
}

/*
//supremeLeader constraints
fact{
	all control : Control , supremeLeader : SupremeLeader | control in supremeLeader.modifiable_control
}

fact{
	all control : Control , supremeLeader : SupremeLeader | control in supremeLeader.visible_control
}

fact {
	all signal : Signal, supremeLeader : SupremeLeader | signal in supremeLeader.modifiable_signal
}

fact {
	all signal : Signal, supremeLeader : SupremeLeader | signal in supremeLeader.visible_signal
}
*/



//other constraints
fact{
	all signal : Signal { one myModule : Module | signal in myModule.provides }
}

fact {
	all control : Control { some composit : Composit | control in composit.submodules }
}



//még nem jó
//minden specialist látja azokat a control - okat amelyek az általa szerkeszthető control-okkal egy
//compositban vannak és a comopsit nem védett.
//minden specialist látja azokat a signal - okat amelyek az általa szerkeszthető control-okkal 
//egy compositban levő controlok illetve a composit által vannak providolva és a comopsit nem
//védett.
// Control látható ha -- constraint

fact{ 
	all spec : Specialist{
				all control : Control | ( /*control.~submodules.protectedIP=False 
								and */ control in spec.modifiable_control ) implies
								control.~submodules.submodules in spec.visible_control
	}
}

//egy control csak akkor látható egy specialist számára ha az általa szerkezthető conrtolok egy 
//compositban vannak vele, és a composit nem védett
fact{
	all control : Control {
		all spec : Specialist |  control in spec.visible_control implies
								spec.modifiable_control in control.~submodules.submodules
	}
}

fact{
	all spec : Specialist {
		all control : Control | control not in spec.visible_control 
								or control.provides in spec.visible_signal
	}
}

fact{
	all spec : Specialist {
		all comp : Composit | spec.modifiable_control not in comp.submodules
							  or comp.provides in spec.visible_signal 
	}
}


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

fact{
	some fanSpec : FanSpecialist{
	some disj o2 , o10, o7, o3, o4, o5, o6, o8, o9, o11, o12 : EObject |
		 o10 in o2.submodules and
		 o7 in o2.submodules and
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
		 o10 in fanSpec.modifiable_control   
}
}


run {} for 15

/*for  /*exactly 8 EObject,
			exactly 5 Control,
			exactly 2 Composit,
			exactly 5 Signal,
			exactly 0 Specialist
*/

	

