/**
	A model of the OAuth 1 protocol

	Author: Eunsuk Kang (eskang@cmu.edu)
	Created: July 15, 2020
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
abstract sig ReqToken extends Data {}
abstract sig UserCred extends Data {}		
abstract sig AccessToken extends Data {}	// access token

one sig idAlice, idEve extends OAuthID {}
one sig requestTokenA, requestTokenB extends ReqToken {}
one sig credAlice, credEve extends UserCred {}
one sig accessTokenAlice, accessTokenEve extends AccessToken {}

abstract sig Session extends Data {}
one sig sessionX extends Session {}
one sig sessionY extends Session {}


/** 
	OAuth components
**/

// Authorization server, which grants OAuthClient access to a resource. 
sig AuthServer in Component {
	creds : OAuthID -> lone UserCred
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

// 0. initiate
// from UserAgent to Client
sig initiate extends CallEvent {
	session : Session
}{
	no args 
	rets = session
	some sender & UserAgent 
	some receiver & MyApp
}

// 1. getRequestToken
// from Client to AuthServer
sig getRequestToken extends CallEvent {
	reqToken : ReqToken		
}{
	no args 
	rets = reqToken
	some sender & Client 
	some receiver & AuthServer
}

// 2. Retrieve request token from the client
// from UserAgent to Client
sig retrieveReqToken extends CallEvent {
	session : Session,
	reqToken : ReqToken			
}{
	args = session
	rets = reqToken
	some sender & UserAgent 
	some receiver & MyApp	
}

// 3. Authentication step
// from UserAgent to AuthServer
// AuthServer authenticates the user and
// returns a corresponding authorization code
sig authorize extends CallEvent {
	userid : OAuthID,
	cred : UserCred,
	reqToken : ReqToken
}{
	args = cred + userid + reqToken
	no rets 
	some UserAgent & sender 
	some AuthServer & receiver
}

// 4. Pass auth code
// from UserAgent to OAuthClient
// User passes the authorization code to the client
sig authorized extends CallEvent {
	session : Session
}{
	args = session
	no rets 
	some sender & UserAgent 
	some receiver & Client
}

// 5. Requesting access token
// from OAuthClient to AuthServer
// The client sends the authorization code directly to the auth server
// to receive an access token
sig getAccessToken extends CallEvent {
	reqToken : ReqToken,
	accessToken : AccessToken
}{
	args = reqToken
	rets = accessToken
	some sender & Client 
	some receiver & AuthServer
}


/** 
	* Instantiation 
	*/
one sig Alice in UserAgent {}{
	this not in AuthServer + Client
	id = idAlice
	cred = credAlice
	owns = cred + idAlice
	// user behavior	
	all o : authorize & sender.this {
		o.userid = id and o.cred = cred
	}

}
one sig Eve in UserAgent {}{
	id = idEve
	cred = credEve
	owns = cred + idEve
}
one sig MyApp in Client {}{
	this not in AuthServer + UserAgent 
	owns = Session

	//  behavior	
	all o : initiate & receiver.this {
		all o' : o.prevs & initiate & receiver.this {
			o.session != o'.session
		}
	}
		
	all o : retrieveReqToken & receiver.this {
		myApp_reqTokens[o, o.session, o.reqToken]
	}
		
	all a : getRequestToken & sender.this {
		a.prev in initiate
	}

	all o : authorized & receiver.this  {
		o.next in getAccessToken and o.next.sender = this
	}

	all o : getAccessToken & sender.this | let o' = o.prev {
		o' in authorized
		myApp_reqTokens[o, o'.(authorized <: session), o.reqToken]
	}
}

pred google_req2access[e : Event, r: ReqToken, a : AccessToken] {
	some e' : e.prevs & authorize & receiver.Google {
		(e'.userid = idAlice and r = e'.reqToken and a = accessTokenAlice) or
		(e'.userid = idEve and r = e'.reqToken and a = accessTokenEve)
	}
}

one sig Google in AuthServer {}{

	this not in Client + UserAgent

	creds = idAlice -> credAlice + idEve -> credEve
	owns = ReqToken + AccessToken + UserCred

	//  behavior	
	all o : authorize & receiver.this {
		o.userid -> o.cred in creds 
		all o' : o.prevs & authorize & receiver.this |
			o.reqToken != o'.reqToken
	}

	all o : getRequestToken & receiver.this {
		all o' : o.prevs & getRequestToken & receiver.this {
			o.reqToken != o'.reqToken
		}
	}

	all o : getAccessToken & receiver.this {
		// AccessTokenReq must provide an authorization grant that corresponds to
		// the access token returned
		google_req2access[o, o.reqToken, o.accessToken]
	}
}


/**
	Security assumptions
**/
fact security_assumptions {
	Eve not in AuthServer
	Eve not in Client

	idAlice not in Eve.owns
	requestTokenA not in Eve.owns
	requestTokenB not in Eve.owns
	credAlice not in Eve.owns
	accessTokenAlice not in Eve.owns
	accessTokenEve not in Eve.owns
	sessionX not in Eve.owns
	sessionY not in Eve.owns 
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

pred myApp_sessions[e : Event, i : Session, u : UserAgent] {
	some e' : e.prevs & procs.MyApp & initiate |
		u in e'.sender and i = e'.session
}

pred myApp_reqTokens[e : Event, i : Session, r : ReqToken] {
	some e' : e.prevs & procs.MyApp & getRequestToken |
			i = e'.prev.(initiate <: session) and r = e'.reqToken
}

pred myApp_accessTokens[e : Event, i : Session, t : AccessToken] {
	some e' : e.prevs & procs.MyApp & getAccessToken |
		t = e'.accessToken and
		myApp_reqTokens[e', i, e'.reqToken] 
}

pred session_integrity_requirement {
	all e : Event, id : Session |
		myApp_accessTokens[e, id, accessTokenAlice] implies	
			not myApp_sessions[e, id, Eve]
}

// property check
run check_session_integrity {
	not session_integrity_requirement
} for 5 but 10 Event, 10 Time, 4 Component

// sample test scenairos
pred scenario1 {
	some e : Event, id : Session |  
		myApp_accessTokens[e, id, accessTokenAlice] 
		and Alice -> id -> e in knows
}
pred scenario2 {
	some e : Event, id : Session |  
		myApp_accessTokens[e, id, accessTokenEve] 
		and Eve -> id -> e in knows
}

run testScenario1 {
	scenario1
} for 4 but 6 Event, 6 Time

run testScenario2 {
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

fun prev : Event -> Event {
	{e1, e2 : Event | e2.at in e1.at.prev }
}

fun next : Event -> Event {
	~this/prev
}

