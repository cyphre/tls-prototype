REBOL [
	title: "TLS 1.0 implementation prototype"
	author: rights: "Richard 'cyphre' Smolak"
	version: 0.0.8
	license: 'MIT
	todo: {
		-cached sessions
		-automagic cert data lookup
		-compatibility with schemes usage (port abstraction)
		-R3 conversion
		-add more cipher suites
		-server role support
		-SSL3.0, TLS1.1 compatibility
		-cert validation
	}
]

tls: context [
	version: #{03 01} ;protocol version used

	server?: false

	protocol-state: none
	
	hash-method: 'sha1
	hash-size: 20
	crypt-method: 'arcfour
	crypt-size: 16	; 128bits
	cipher-suite: #{00 05} ;TLS_RSA_WITH_RC4_128_SHA

	client-crypt-key:
	client-mac-key:
	server-crypt-key:
	server-mac-key: none
	
	seq-num: 0
	
	msg: make binary! 4096
	handshake-messages: make binary! 4096 ;all messages from Handshake records except 'HelloRequest's
	encrypted?: false
	port: client-random: server-random: pre-master-secret: master-secret: key-block: certificate: pub-key: pub-exp: none

	encrypt-port: decrypt-port: none
	
	emit: func [
		code [block! binary!]
	][
		repend msg code
	]

	to-bin: func [
		val [integer!]
		width [integer!]
	][
		skip tail debase/base to-hex val 16 negate width
	]

	open-port: func [
		addr [url!]
	][
		port: open/binary/direct addr
	]

	read-proto-states: [
		client-hello [server-hello]
		server-hello [certificate]
		certificate [server-hello-done]
		server-hello-done []
		finished [change-cipher-spec alert]
		change-cipher-spec [encrypted-handshake]
		application [application alert]
		alert []
	]

	write-proto-states: [
		server-hello-done [client-key-exchange]
		client-key-exchange [change-cipher-spec]
		change-cipher-spec [finished]
		encrypted-handshake [application]
	]
	
	get-next-proto-state: func [
		/write-state "default is read state"
		/local
			next-state
	][
		all [
			next-state: all [next-state: select/only/skip either write-state [write-proto-states][read-proto-states] protocol-state 2 first next-state]
			not empty? next-state
			next-state
		]
	]
	
	update-proto-state: func [
		new-state [word!]
		/write-state
		/local
			next-state
	][
;		print [protocol-state "->" new-state write-state]
		either any [
			none? protocol-state
			all [
				next-state: apply :get-next-proto-state [write-state]
				find next-state new-state
			]
		][
			protocol-state: new-state
		][
			make error! "invalid protocol state"
		]
	]
	
	insert-port: func [
		msg [binary!]
		/local
			result data len proto new-state next-state record enc?
	][
		result: copy #{}
		record: copy #{}
;		print ["writing bytes:" length? msg]
		insert port msg

		
		
		while [
			data: copy/part port 5
		][
			unless proto: select protocol-types data/1 [
				make error! "unknown/invalid protocol type"
			]						

			append clear record data
			
			len: to-integer copy/part at data 4 2

;			print ["reading bytes:" len]
			data: copy/part port len
;			print ["received bytes:" length? data]

			if len <> length? data [
				make error! ["invalid length data"]
			]

			append record data

			new-state: either proto = 'handshake [
				either enc? [
					'encrypted-handshake
				][
					select message-types record/6
				]
			][
				proto
			]
		
			update-proto-state new-state

			if protocol-state = 'change-cipher-spec [enc?: true]
			
			append result record

			next-state: get-next-proto-state
			
;			print ["State:" protocol-state "-->" next-state]

			unless next-state [return parse-response result]
		]
;		print "Connection closed"
		return parse-response result
	]

	write-port: func [
		commands [block!]
		/local arg cmd
	][
		clear msg
		parse commands [
			some [
				set cmd [
					'client-hello (client-hello)
					| 'client-key-exchange (client-key-exchange)
					| 'change-cipher-spec (change-cipher-spec)
					| 'finished (encrypted-handshake-msg finished)
					| 'application  set arg [string! | binary!] (application-data arg)
				] (
;					print [seq-num "<--" cmd]
					seq-num: seq-num + 1
					update-proto-state/write-state cmd
				)
			]
		]
		insert-port msg
	]
	
	;ASN.1 format parser code
	
	universal-tags: [
		eoc
		boolean
		integer
		bit-string
		octet-string
		null
		object-identifier
		object-descriptor
		external
		real
		enumerated
		embedded-pdv
		utf8string
		relative-oid
		undefined
		undefined
		sequence
		set
		numeric-string
		printable-string
		t61-string
		videotex-string
		ia5-string
		utc-time
		generalized-time
		graphic-string
		visible-string
		general-string
		universal-string
		character-string
		bmp-string
	]

	class-types: [universal application context-specific private]

	parse-asn: func [
		data [binary!]
		/local
			mode d constructed? class tag ln length result val
	][
		result: copy []
		mode: 'type

		while [d: data/1][
			switch mode [
				type [
					constructed?: to logic! (and d 32)
					class: pick class-types 1 + shift d 6
					 
					switch class [
						universal [
							tag: pick universal-tags 1 + and d 31
						]
						context-specific [
							tag: class
							val: and d 31
						]
					]
					mode: 'length				
				]
			
				length [
					length: and d 127
					unless zero? and d 128 [
						;long form
						ln: length
						length: to integer! copy/part next data length
						data: skip data ln
					]
					either zero? length [
						append/only result compose/deep [(tag) [(either constructed? ["constructed"]["primitive"]) (index? data) (length) #[none]]]
						mode: 'type
					][
						mode: 'value
					]
				]
				
				value [
					switch class [
						universal [
							val: copy/part data length
							append/only result compose/deep [(tag) [(either constructed? ["constructed"]["primitive"]) (index? data) (length) (either constructed? [none][val])]]
							if constructed? [
								poke second last result 4	parse-asn val
							]
						]
						
						context-specific [
							append/only result compose/deep [(tag) [(val) (length)]]
							parse-asn copy/part data length
						]
					]

					data: skip data length - 1
					mode: 'type
				]
			]
			
			data: next data
		]
		result
	]
	
	;TLS protocol code
	
	client-hello: has [beg len][
		;generate client random struct
		client-random: to-bin to-integer difference now/precise 1-Jan-1970 4
		random/seed now/time/precise
		loop 28 [append client-random to-char (random/secure 256) - 1]

		beg: length? msg
		emit [
			#{16}			; protocol type (22=Handshake)
			version			; protocol version (3|1 = TLS1.0)
			#{00 00}		; length of SSL record data
			#{01}			; protocol message type	(1=ClientHello)
			#{00 00 00} 	; protocol message length
			version			; max supported version by client (TLS1.0)
			client-random	; random struct (4 bytes gmt unix time + 28 random bytes)
			#{00}			; session ID length
			#{00 02}		; cipher suites length (only one suit for testing at the moment)
			cipher-suite	; cipher suites list (0005 = TLS_RSA_WITH_RC4_128_SHA) (0004 = TLS_RSA_WITH_RC4_128_MD5) etc.
			#{01}			; compression method length
			#{00}			; no compression
		]
		
		; set the correct msg lengths
		change at msg beg + 7 to-bin len: length? at msg beg + 10 3
		change at msg beg + 4 to-bin len + 4 2

		append clear handshake-messages copy at msg beg + 6
		
		return msg
	]

	client-key-exchange: has [
		rsa-key pms-enc beg len
	][
		;generate pre-master-secret
		pre-master-secret: copy version
		random/seed now/time/precise
		loop 46 [append pre-master-secret to-char (random/secure 256) - 1]
		
		;encrypt pre-master-secret
		rsa-key: rsa-make-key
		rsa-key/e: pub-exp
		rsa-key/n: pub-key
		pms-enc: rsa-encrypt/padding rsa-key pre-master-secret 'pkcs1

		beg: length? msg
		emit [
			#{16}			; protocol type (22=Handshake)
			version			; protocol version (3|1 = TLS1.0)
			#{00 00}		; length of SSL record data
			#{10}			; protocol message type	(16=ClientKeyExchange)
			#{00 00 00} 	; protocol message length
			to-bin length? pms-enc 2	;length of the key (2 bytes)
			pms-enc
		]

		; set the correct msg lengths
		change at msg beg + 7 to-bin len: length? at msg beg + 10 3
		change at msg beg + 4 to-bin len + 4 2

		append handshake-messages copy at msg beg + 6

		;make all secrue data
		make-master-secret pre-master-secret
		make-key-block

		;update keys
		client-mac-key: copy/part key-block hash-size
		server-mac-key: copy/part skip key-block hash-size hash-size
		client-crypt-key: copy/part skip key-block 2 * hash-size crypt-size	
		server-crypt-key: copy/part skip key-block 2 * hash-size + crypt-size crypt-size
		
		return msg
	]


	change-cipher-spec: does [
		emit [
			#{14} ; protocol type (20=ChangeCipherSpec)
			version			; protocol version (3|1 = TLS1.0)
			#{00 01}		; length of SSL record data
			#{01}			; CCS protocol type
		]
		return msg
	]

	encrypted-handshake-msg: func [
		message [binary!]
		/local
			plain-msg
	][
		plain-msg: message
		message: encrypt-data/type message #{16}
		emit [
			#{16}			; protocol type (22=Handshake)
			version			; protocol version (3|1 = TLS1.0)
			to-bin length? message 2	; length of SSL record data
			message
		]
		append handshake-messages plain-msg
		return msg
	]

	application-data: func [
		message [binary! string!]
	][
		message: encrypt-data as-binary message
		emit [
			#{17}			; protocol type (23=Application)
			version			; protocol version (3|1 = TLS1.0)
			to-bin length? message 2	; length of SSL record data			
			message
		]
		return msg
	]

	finished: does [
		seq-num: 0
		return rejoin [
			#{14}		; protocol message type	(20=Finished)
			#{00 00 0c} ; protocol message length (12 bytes)
			prf master-secret either server? ["server finished"]["client finished"] rejoin [
				checksum/method handshake-messages 'md5 checksum/method handshake-messages 'sha1
			] 12
		]
	]
	
	encrypt-data: func [
		data [binary!]
		/type
			msg-type [binary!] "application data is default"
		/local	
			crypt-data
	][
		unless encrypt-port [
			encrypt-port: make port! [
				scheme: 'crypt
				algorithm: crypt-method
				direction: 'encrypt
				strength: crypt-size * 8
				key: client-crypt-key
				padding: false
			]
			open encrypt-port
		]

		insert encrypt-port rejoin [
			data
			;MAC code
			checksum/method/key rejoin [
				#{00000000} to-bin seq-num 4		;sequence number (limited to 32-bits here)			
				any [msg-type #{17}]				;msg type
				version								;version
				to-bin length? data 2				;msg content length				
				data								;msg content
			] hash-method client-mac-key
		]
		update encrypt-port
		crypt-data: copy encrypt-port
		return crypt-data
	]	

	decrypt-data: func [
		data [binary!]
		/local	
			crypt-data
	][
		unless decrypt-port [
			decrypt-port: make port! [
				scheme: 'crypt
				algorithm: crypt-method
				direction: 'decrypt
				strength: crypt-size * 8
				key: server-crypt-key
				padding: false
			]

			open decrypt-port
		]
		insert decrypt-port data
		update decrypt-port
		crypt-data: copy decrypt-port
		return crypt-data
	]	
	
	protocol-types: [
		20 change-cipher-spec
		21 alert
		22 handshake
		23 application
	]
	
	message-types: [
		0 hello-request
		1 client-hello 
		2 server-hello
		11 certificate
		12 server-key-exchange
		13 certificate-request
		14 server-hello-done
		15 certificate-verify
		16 client-key-exchange
		20 finished
	]
	
	alert-descriptions: [
		0 "Close notify"
		10 "Unexpected message"
		20 "Bad record MAC"
		21 "Decryption failed"
		22 "Record overflow"
		30 "Decompression failure"
		40 "Handshake failure"
		41 "No certificate"
		42 "Bad certificate"   
		43 "Unsupported certificate"
		44 "Certificate revoked"
		45 "Certificate expired"
		46 "Certificate unknown"
		47 "Illegal parameter"
		48 "Unknown CA"
		49 "Access denied"
		50 "Decode error"
		51 "Decrypt error"
		60 "Export restriction"
		70 "Protocol version"
		71 "Insufficient security"
		80 "Internal error"
		90 "User cancelled"
	   100 "No renegotiation"
	   110 "Unsupported extension"
	]

	parse-protocol: func [
		data [binary!]
		/local proto
	][
		unless proto: select protocol-types data/1 [
			make error! "unknown/invalid protocol type"
		]						
		return context [
			type: proto
			version: pick [ssl-v3 tls-v1.0 tls-v1.1] data/3 + 1
			length: to-integer copy/part at data 4 2
			messages: copy/part at data 6 length
		]
	]
	
	parse-messages: func [
		proto [object!]
		/local
			result data msg-type len clen msg-content mac msg-obj
	][
		result: copy []
		data: proto/messages
		
		if encrypted? [
			change data decrypt-data data
;			print ["decrypted:" data]
		]
;		print [seq-num "-->" proto/type]
		switch proto/type [
			alert [
				append result reduce [
					context [
						level: any [pick [warning fatal] data/1 'unknown]
						description: any [select alert-descriptions data/2 "unknown"]
					]
				]
			]
			handshake [
				while [data/1][
					len: to-integer copy/part at data 2 3
					append result switch msg-type: select message-types data/1 [
						server-hello [
							msg-content: copy/part at data 7 len
							
							msg-obj: context [
								type: msg-type
								version: pick [ssl-v3 tls-v1.0 tls-v1.1] data/6 + 1
								length: len
								server-random: copy/part msg-content 32
								session-id: copy/part at msg-content 34 msg-content/33
								cipher-suite: copy/part at msg-content 34 + msg-content/33 2
								compression-method-length: first at msg-content 36 + msg-content/33
								compression-method: either compression-method-length = 0 [none][copy/part at msg-content 37 + msg-content/33 compression-method-length]
							]
							server-random: msg-obj/server-random
							msg-obj
						]
						certificate [
							msg-content: copy/part at data 5 len
							msg-obj: context [
								type: msg-type
								length: len
								certificates-length: to-integer copy/part msg-content 3
								certificate-list: copy []
								while [msg-content/1][
									if 0 < clen: to-integer copy/part skip msg-content 3 3 [
										append certificate-list copy/part at msg-content 7 clen
									]
									msg-content: skip msg-content 3 + clen										
								]
							]
							;no cert validation - just set it to be used
							certificate: parse-asn msg-obj/certificate-list/1
							
							;get the public key and exponent (hardcoded for now)
							pub-key: parse-asn next
;									certificate/1/sequence/4/1/sequence/4/6/sequence/4/2/bit-string/4
									certificate/1/sequence/4/1/sequence/4/7/sequence/4/2/bit-string/4
							pub-exp: pub-key/1/sequence/4/2/integer/4
							pub-key: next pub-key/1/sequence/4/1/integer/4
							
							msg-obj
						]
						server-hello-done [
							context [
								type: msg-type
								length: len
							]
						]
						client-hello [
							msg-content: copy/part at data 7 len
							context [
								type: msg-type
								version: pick [ssl-v3 tls-v1.0 tls-v1.1] data/6 + 1
								length: len
								content: msg-content
							]
						]
						finished [
							msg-content: copy/part at data 5 len
							either msg-content <> prf master-secret either server? ["client finished"]["server finished"] rejoin [checksum/method handshake-messages 'md5 checksum/method handshake-messages 'sha1] 12 [
								make error! "Bad 'finished' MAC"
							][
;								print "FINISHED MAC verify: OK"
							]
							context [
								type: msg-type
								length: len
								content: msg-content
							]
						]
					]

					append handshake-messages copy/part data len + 4

					data: skip data len + either encrypted? [
						;check the MAC
						mac: copy/part skip data len + 4 hash-size
						if mac <> checksum/method/key rejoin [
								#{00000000} to-bin seq-num 4			;sequence number (limited to 32-bits here)
								#{16}										;msg type
								version										;version
								to-bin len + 4 2							;msg content length												
								copy/part data len + 4
							] hash-method server-mac-key
						[
							make error! "Bad record MAC"
						]
						4 + hash-size
					][
						4
					]
				]
			]
			change-cipher-spec [
				seq-num: -1
				encrypted?: true
				append result context [
					type: 'ccs-message-type
				]
			]
			application [
				append result context [
					type: 'app-data
					content: copy/part data (length? data) - hash-size
				]
			]
		]
		seq-num: seq-num + 1
		return result
	]
	
	parse-response: func [
		msg [binary!]
		/local
			result proto messages len
	][
		result: copy []
		len: 0
		until [
			append result proto: parse-protocol msg
			either empty? messages: parse-messages proto [
				make error! "unknown/invalid protocol message"
			][
				proto/messages: messages
			]
			tail? msg: skip msg proto/length + 5
		]
		return result
	]
	
	prf: func [
		secret [binary!]
		label [string! binary!]
		seed [binary!]
		output-length [integer!]
		/local
			len mid s-1 s-2 a p-sha1 p-md5
	][
		len: length? secret
		mid: to-integer .5 * (len + either odd? len [1][0])
	
		s-1: copy/part secret mid
		s-2: copy at secret mid + either odd? len [0][1]

		seed: rejoin [#{} label seed]
		
		p-md5: copy #{}
		a: seed ;A(0)
		while [output-length > length? p-md5][
			a: checksum/method/key a 'md5 s-1 ;A(n)
			append p-md5 checksum/method/key rejoin [a seed] 'md5 s-1

		]

		p-sha1: copy #{}
		a: seed ;A(0)
		while [output-length > length? p-sha1][
			a: checksum/method/key a 'sha1 s-2 ;A(n)
			append p-sha1 checksum/method/key rejoin [a seed] 'sha1 s-2
		]
		
		return xor copy/part p-md5 output-length copy/part p-sha1 output-length
	]

	make-key-block: does [
		key-block: prf master-secret "key expansion" rejoin [server-random client-random] 2 * hash-size + (2 * crypt-size)
	]
	
	make-master-secret: func [
		pre-master-secret [binary!]
	][
		master-secret: prf pre-master-secret "master secret" rejoin [client-random server-random] 48
	]
	
	init: does [
		seq-num: 0
		protocol-state: none
		encrypted?: false
		if port [close port]		
		if encrypt-port [
			close encrypt-port
			encrypt-port: none
		]
		if decrypt-port [
			close decrypt-port
			decrypt-port: none
		]
	]

	;simplified example of the protocol usage to get response using HTTPS request
	read-url: func [
		url [url!]
		/local
			resp data
	][
		init
		url: decode-url url
		open-port to-url reduce ['tcp rejoin [url/host ":" any [url/port-id 443]]]
		resp: write-port [client-hello]
		if resp/1/type = 'handshake [
			resp: write-port [
				client-key-exchange
				change-cipher-spec
				finished
			]
			
			foreach proto resp [
				if proto/type = 'handshake [
					foreach msg proto/messages [
						if msg/type = 'finished [
							;server sent "finished" msg so we can finally start sending app data
							;get the requested page
							resp: write-port compose [application (rejoin [
								"GET /" any [url/path ""] any [url/target ""] " HTTP/1.0^/"
								"Host: " url/host "^/^/"
							])]
							data: copy {}
							foreach proto resp [
								if proto/type = 'application [
									foreach msg proto/messages [
										if msg/type = 'app-data [
											append data msg/content
										]
									]
								]
							]
							unless empty? data [return data]
						]
					]
				]
			]
		]
		resp
	]
		
]

;DEMO

print "loading HTTPS page..."
probe tls/read-url tcp://accounts.google.com/ServiceLogin ;port is 443 by default if not specified
;tcp://login.yahoo.com:443

halt
