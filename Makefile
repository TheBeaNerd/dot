include $(ACL2_SYSTEM_BOOKS)/Makefile-generic

%.cert: %.lisp
	$(ACL2_SYSTEM_BOOKS)/build/cert.pl $@

all: local

local:
	$(ACL2_SYSTEM_BOOKS)/build/cert.pl *.lisp

clean: cleanup

cleanup:
	$(RM) -rf Makefile-tmp
