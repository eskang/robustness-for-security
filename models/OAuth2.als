/**
	A model of the OAuth 2 protocol

	Author: Eunsuk Kang (eskang@cmu.edu)
	Created: July 13, 2020
	Edited: July 27, 2020
**/

open util/ordering[Time] as TO

/**
	Basics: Process & Events
**/
sig Time {}

abstract sig Process {
	events : set Event 
}
abstract sig Event {
	at : Time	// time at which this event takes place
}
fact {
	// At every time step, there's exactly one event that takes place
	all t : Time - last | one e : Event | e.at = t
}

/**
	Components
**/
abstract sig Component extends Process {
	owns : set Data
}
abstract sig CallEvent extends Event {
	sender, receiver : Component,
	args : set Data,
	rets : set Data,
}{
	this in sender.events
	this in receiver.events
}

/**
	OAuth-related data
**/
abstract sig Data {}

abstract sig OAuthID extends Data {}
//abstract sig Resource extends Data {}
// Tokens
abstract sig Token extends Data {}
abstract sig AuthCode extends Token {}		// authorization grant
abstract sig UserCred extends Token {}		
abstract sig AccessToken extends Token {}	// access token
// instantiations
one sig id_Alice, id_Eve extends OAuthID {}
//one sig AliceRes, EveRes extends Resource {}
one sig code_Alice, code_Eve extends AuthCode {}
one sig cred_Alice, cred_Eve extends UserCred {}
one sig token_Alice, token_Eve extends AccessToken {}
// sessions
abstract sig Session extends Data {}
one sig session_X extends Session {}
one sig session_Y extends Session {}

/** 
	OAuth components
**/

// Authorization server, which grants OAuthClient access to a resource. 
sig AuthServer in Component {
	tokens : AuthCode -> AccessToken,
	codes : UserCred -> AuthCode,
	creds : OAuthID -> lone UserCred,
}

// Client requesting access to a resource 
sig Client in Component {}

// User/owner of a resource
sig UserAgent in Component {
	id : OAuthID,
	cred : UserCred
}


/**
	* Operations that represent different steps of the OAuth protocol
	*/

// 0. Initiation step
sig initiate extends CallEvent {
	session : Session
}{
	no args 
	rets = session
	some sender & UserAgent 
	some receiver & MyApp
}

// 1. Authentication step
// from UserAgent to AuthServer
// AuthServer authenticates the user and
// returns a corresponding authorization code
sig authorize extends CallEvent {
	userid : OAuthID,
	cred : UserCred,
	code : AuthCode	
}{
	args = cred + userid
	rets = code
	some UserAgent & sender 
	some AuthServer & receiver
}

// 2. Pass auth code
// from UserAgent to OAuthClient
// User passes the authorization code to the client
sig forward extends CallEvent {
	session : Session,
	code : AuthCode
}{
	args = code + session
	no rets 
	some sender & UserAgent 
	some receiver & Client
}

// 3. Requesting access token
// from OAuthClient to AuthServer
// The client sends the authorization code directly to the auth server
// to receive an access token
sig getAccessToken extends CallEvent {
	code : AuthCode,
	token : AccessToken
}{
	args = code
	rets = token
	some sender & Client 
	some receiver & AuthServer
}

/** 
	* Instantiation 
	*/
one sig Alice in UserAgent {}{

	this not in AuthServer + Client

	id = id_Alice
	cred = cred_Alice
	owns = cred + id_Alice
	
	// user behavior
	all o : authorize & sender.this {
		o.userid = id and o.cred = cred
	}
}

one sig Eve in UserAgent {}{
	id = id_Eve
	cred = cred_Eve
	cred + id_Eve in owns
}

one sig MyApp in Client {}{

	this not in AuthServer + UserAgent 

	owns = Session

	// MyApp behavior
	all o : initiate & receiver.this {
		all o' : o.prevs & receiver.this & initiate {
			o.session != o'.session
		}
	}
	all f : forward & sender.this {
		some o : f.prevs & sender.this & initiate {
			o.session = f.session
		}
	}
}

one sig Google in AuthServer {}{

	this not in Client + UserAgent

	tokens = code_Alice -> token_Alice + code_Eve -> token_Eve
	codes = cred_Alice -> code_Alice + cred_Eve -> code_Eve
	creds = id_Alice -> cred_Alice + id_Eve -> cred_Eve

	// AuthServer behavior
	all o : authorize & receiver.this {
		o.userid -> o.cred in creds
		// AuthReq must provide a OAuth user credential that corresponds to
		// the authorization grant returned 	
		o.cred -> o.code in codes
	}

	all o : getAccessToken & receiver.this {
		// AccessTokenReq must provide an authorization grant that corresponds to
		// the access token returned
		o.code -> o.token in tokens
	}

}

/**
	Security assumptions
**/
fact security_assumptions {
	Eve not in AuthServer
	Eve not in Client
		
	id_Alice not in Eve.owns
	code_Alice not in Eve.owns
	code_Eve not in Eve.owns
	cred_Alice not in Eve.owns
	token_Alice not in Eve.owns
	token_Eve not in Eve.owns 
	session_X not in Eve.owns
	session_Y not in Eve.owns 
}

/**
	Process behavior
**/
fun knows : Process -> Data -> Event {
	{ p : Process, d : Data, e : Event |
		d in p.owns or
		some e' : e.prevs |
			(d in e'.args and p in e'.receiver) or
			(d in e'.rets and p in e'.sender)
	}
}

fact processBehavior {
	// Process must have access to data arguments as part of an event
	all e : Event, p : Process |	
		(p in e.sender implies e.args in p.knows.e) and
		(p in e.receiver implies e.rets in e.args + p.knows.e)
}

/**
	Properties
**/

fun procs : Event -> Process {
	{e : Event, p : Process | p in e.(sender + receiver) }
}

// User initiates a session "i" with MyApp
pred myApp_sessions[e : Event, i : Session, u : UserAgent] {
	some e' : e.prevs & procs.MyApp & initiate |
		u in e'.sender and i = e'.session
}

pred myApp_codes[e : Event, i : Session, c : AuthCode] {
	// MyApp receives auth. code "c" that is associated with session "i" 
	some e' : e.prevs & procs.MyApp, l : e' & forward |
			i = l.session and c = l.code	
}

pred myApp_tokens[e : Event, i : Session, t : AccessToken] {
	// MyApp receives an access token for the authorization code
	// that is associated with session "i"
	some e' : e.prevs & procs.MyApp, l : e' & getAccessToken |
		t = l.token and
		myApp_codes[e', i, l.code] 
}

pred session_integrity_requirement {
	all e : Event, id : Session |
		// Alice's token is not associated with Eve's session
		myApp_tokens[e, id, token_Alice] implies	
			not myApp_sessions[e, id, Eve]
}

// Property check
run check_session_integrity {
	not  session_integrity_requirement 
} for 6 but 10 Event, 10 Time, 4 Component


// Sample test scenarios
pred scenario1 {
	some e : Event, id : Session |  
		myApp_tokens[e, id, token_Alice] 
		and Alice -> id -> e in knows
}
pred scenario2 {
	some e : Event, id : Session |  
		myApp_tokens[e, id, token_Eve] 
		and Eve -> id -> e in knows
}
run test_scenario1 {
	scenario1
} for 4 but 6 Event, 6 Time

run test_scenario2 {
	scenario2
} for 4 but 6 Event, 6 Time

/**
	Helper functions
**/
fun _relevant : Event -> Time {
	{e : Event, t : Time | e in at.t }
}

fun _relevant : Component -> Time {
	{c : Component, t : Time | c in at.t.(receiver + sender) or t = TO/last}
}

fun TO : Component -> Component -> Time {
	{c1, c2 : Component, t : Time | let e = at.t | c1 = e.sender and c2 = e.receiver } 
}

fun prevs : Event -> Event {
	{e1, e2 : Event | e2.at in e1.at.prevs }
}

