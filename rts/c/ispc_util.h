// TODO(pema): Error handling

typedef unsigned char uchar;

static void free(void* ptr) {
  delete ptr;
}

static void free(void* uniform ptr) {
  if (programIndex == 0) {
    delete ptr;
  }
}

static uniform int lexical_realloc_ispc(unsigned char uniform * uniform * uniform ptr,
                                        int64_t uniform * uniform old_size,
                                        uniform int64_t new_size) {
  if (*ptr != NULL) free(*ptr);
  unsigned char uniform * uniform alloc = uniform new uchar[new_size];
  *ptr = alloc;
  *old_size = new_size;
  return FUTHARK_SUCCESS;
}

static uniform int lexical_realloc_ispc(unsigned char uniform * uniform * uniform ptr,
                                        int64_t uniform * uniform old_size,
                                        varying int64_t new_size) {
  return lexical_realloc_ispc(ptr, old_size, extract(new_size, 0));
}

static uniform int lexical_realloc_ispc(unsigned char uniform * varying * uniform ptr,
                                        int64_t uniform * varying old_size,
                                        varying int64_t new_size) {
  if (*ptr != NULL) free(*ptr);
  unsigned char* alloc = new uchar[new_size];
  *ptr = alloc;
  *old_size = new_size;
  return FUTHARK_SUCCESS;
}

static uniform int lexical_realloc_ispc(unsigned char uniform * varying * uniform ptr,
                                        int64_t varying * uniform old_size,
                                        varying int64_t new_size) {
  return lexical_realloc_ispc(ptr, (uniform int64_t * varying)old_size, new_size);
}

static uniform int lexical_realloc_ispc(unsigned char uniform * varying * uniform ptr,
                                        size_t varying * uniform old_size,
                                        varying int64_t new_size) {
  if (*ptr != NULL) free(*ptr);
  unsigned char* alloc = new uchar[new_size];
  *ptr = alloc;
  *old_size = new_size;
  return FUTHARK_SUCCESS;
}