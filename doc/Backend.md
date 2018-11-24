
== Combinator set

Jeder Kombinator mehr erhöht die Anzahl der zu generierenden Fälle um nodeSize * bisherigeFälle.
Beispiel 5 Knoten: KS:   42 * (2 ^ 6) = 2688
Beispiel 5 Knoten: KSBC:   42 * (4 ^ 6) = 172032
Beispiel 5 Knoten: IKSC:   42 * ()
Beispiel 5 Knoten: KSIBC:   42 * (5 ^ 6) = 656250

Nehmen wir Beispiel predecessor, Anzahl Knoten:

KS: 49 509552245179617138054608572 * (2 ^ 24) = 8548868080663395522443987807895552
IKSC:                                                             
KSBC: 24 1289904147324 * (4 ^ 24) =                    363075739827001485944684544
KSIBC: 20 6564120420 * (5 ^ 24) =                      391252065896987915039062500

Bei diesem Beispiel wäre KSBC das Optimum

=== Arbeitshypothese: KSBC wird genutzt

== Abschätzung der Abdeckung in Abhängigkeit

2 ^ 31 = 2147483648 würde für 2 Milliarden Entries reichen (68 GByte Lookup table)

Welche Node size wird etwa abgedeckt:
128 MB = 128000000  / 4 = 32.000.000 Entries = 32 Millionen entries
bei 4 Kombinatoren bis node size 9 - 7
bei 2 Kombinatoren               10 - 11

catalan 12 = 208012
2 Kominatoren = 208012 * (2 ^ 12) * 4 Byte = 3408068608 Byte = 3,4 GByte
4 Kominatoren = 208012 * (4 ^ 12) * 4 Byte = 13959449018368 Byte = *** 13 TByte

catalan 11 = 58786
2 Kominatoren = 58786 * (2 ^ 11) * 4 Byte = 481574912 Byte = Prod ~ 481 MB
4 Kominatoren = 58786 * (4 ^ 11) * 4 Byte = 986265419776 Byte = ~ 1 TByte

catalan 10 = 16796
2 Kominatoren = 16796 * (2 ^ 10) * 4 Byte = 68796416 Byte = Test ~ 68 MB
4 Kominatoren = 16796 * (4 ^ 10) * 4 Byte =  70447529984 Byte ~ 70 GByte

catalan 9 = 4862
2 Kominatoren = 4862 * (2 ^ 9) * 4 Byte = 9957376 Byte = ~ 10 MB
4 Kominatoren = 4862 * (4 ^ 9) * 4 Byte = 5098176512 Byte = 5 GB

catalan 8 = 1034
2 Kominatoren = 1034 * (2 ^ 8) * 4 Byte = 1058816 Byte = ~ 1 MB
4 Kominatoren = 1034 * (4 ^ 8) * 4 Byte =  271056896 = 270  MB

catalan 7 = 429
2 Kominatoren = 429 * (2 ^ 7) * 4 = 219648 Byte = ~ 219 KByte
4 Kominatoren = 429 * (4 ^ 7) * 4 Byte =  28114944 = 28  MB


=== Arbeitshypothese:

128 Millionen Entrie Produktion = 512 MB
4 Millionen Entries Test = 16 MB

Production
512 MB = 512000000 Byte / 4 = 128.000.000 Entries = 128 Millionen entries
bei 4 Kombinatoren bis node size 9 - 7

Test
16 MB = 16000000 Byte / 4 = 4.000.000 4 Millionen Entries
