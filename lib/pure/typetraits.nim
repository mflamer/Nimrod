#
#
#            Nimrod's Runtime Library
#        (c) Copyright 2012 Nimrod Contributors
#
#    See the file "copying.txt", included in this
#    distribution, for details about the copyright.
#

## This module defines compile-time reflection procs for
## working with types

proc name*(t: typedesc): string {.magic: "TypeTrait".}
  ## Returns the name of the given type

proc name0*(t: typedesc): string {.magic: "TypeTrait".}
  ## Returns the name of the given type 

proc name1*(t: typedesc): string {.magic: "TypeTrait".}
  ## Returns the name of the given type    

proc arity*(t: typedesc): int {.magic: "TypeTrait".}
  ## Returns the arity of the given type

#proc procParamTypes*(t: typedesc): seq[typedesc] {.magic: "TypeTrait".}
#  ## Returns the arity of the given type

proc procReturnType*(t: typedesc): typedesc {.magic: "TypeTrait".}
  ## Returns the arity of the given type    