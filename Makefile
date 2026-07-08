# Standalone Lake projects for the RQ1 case studies
CASE_STUDIES := $(shell find rq1_case_studies -type d -name lean_proofs)

.PHONY: all flex case-studies $(CASE_STUDIES) clean

all: flex case-studies

# Build the Flex library itself (root Lake project)
flex:
	lake build

case-studies: $(CASE_STUDIES)

# Each case study requires Flex via a path dependency, so build Flex first
$(CASE_STUDIES): flex
	cd $@ && lake build

clean:
	lake clean
	@for d in $(CASE_STUDIES); do \
		echo "Cleaning $$d"; \
		(cd $$d && lake clean); \
	done
