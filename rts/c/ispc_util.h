// TODO(pema): Error handling

#ifndef __ISPC_STRUCT_memblock__
#define __ISPC_STRUCT_memblock__
struct memblock {
    int32_t * references;
    uint8_t * mem;
    int64_t size;
    const int8_t * desc;
};
#endif



typedef unsigned char uchar;

static inline void free(void* ptr) {
  delete ptr;
}

static inline void free(void* uniform ptr) {
  if (programIndex == 0) {
    delete ptr;
  }
}

// TODO(pema): Rename
static inline uniform int lexical_realloc_ispc(unsigned char uniform * uniform * uniform ptr,
                                        int64_t uniform * uniform old_size,
                                        uniform int64_t new_size) {
  if (*ptr != NULL) free(*ptr);
  unsigned char uniform * uniform alloc = uniform new uchar[new_size];
  *ptr = alloc;
  *old_size = new_size;
  return FUTHARK_SUCCESS;
}

static inline uniform int lexical_realloc_ispc(unsigned char uniform * uniform * uniform ptr,
                                        int64_t uniform * uniform old_size,
                                        varying int64_t new_size) {
  return lexical_realloc_ispc(ptr, old_size, reduce_max(new_size));
}

static inline uniform int lexical_realloc_ispc(unsigned char uniform * varying * uniform ptr,
                                        int64_t uniform * varying old_size,
                                        varying int64_t new_size) {
  if (*ptr != NULL) free(*ptr);
  unsigned char* alloc = new uchar[new_size];
  *ptr = alloc;
  *old_size = new_size;
  return FUTHARK_SUCCESS;
}

static inline uniform int lexical_realloc_ispc(unsigned char uniform * varying * uniform ptr,
                                        int64_t varying * uniform old_size,
                                        varying int64_t new_size) {
  return lexical_realloc_ispc(ptr, (uniform int64_t * varying)old_size, new_size);
}

// TODO(pema): Don't use size_t, it is evil!!!!
static inline uniform int lexical_realloc_ispc(unsigned char uniform * varying * uniform ptr,
                                        size_t varying * uniform old_size,
                                        varying int64_t new_size) {
  if (*ptr != NULL) free(*ptr);
  unsigned char* alloc = new uchar[new_size];
  *ptr = alloc;
  *old_size = new_size;
  return FUTHARK_SUCCESS;
}

static inline uniform int lexical_realloc_ispc(unsigned char varying * uniform * uniform ptr,
                                        size_t varying * uniform old_size,
                                        uniform int64_t new_size) {
  if (*ptr != NULL) free(*ptr);
  varying unsigned char* uniform alloc = uniform new varying uchar[new_size];
  *ptr = alloc;
  *old_size = new_size;
  return FUTHARK_SUCCESS;
}

static inline uniform int lexical_realloc_ispc(unsigned char varying * uniform * uniform ptr,
                                        size_t varying * uniform old_size,
                                        varying int64_t new_size) {
  return lexical_realloc_ispc(ptr, old_size, reduce_max(new_size));
}

uniform char dummy_error = 0;

extern "C" unmasked uniform int memblock_unref(uniform struct futhark_context * uniform ctx,
					                                     uniform struct memblock * uniform lhs,
					                                     uniform const char * uniform lhs_desc);

static uniform int memblock_unref(uniform struct futhark_context * varying ctx,
				                          uniform struct memblock * varying lhs)
{
  uniform int err = 0;

  foreach_active(i){
    err |= memblock_unref((uniform struct futhark_context * uniform)(extract((varying int64_t)ctx,i)),
		   (uniform struct memblock * uniform)(extract((varying int64_t)lhs,i)),
		   &dummy_error);
  }

  return err;
}
static uniform int memblock_unref(uniform struct futhark_context * uniform ctx,
				                          varying struct memblock * uniform lhs)
{
  uniform int err = 0;

  varying struct memblock _lhs = *lhs;
  uniform struct memblock aos[programCount];
  aos[programIndex] = _lhs;

  foreach_active(i){
    err |= memblock_unref(ctx,
		   &aos[i],
		   &dummy_error);
  }

  *lhs = aos[programIndex];

  return err;
}

extern "C" unmasked uniform int memblock_alloc(uniform struct futhark_context * uniform ctx,
				                                       uniform struct memblock * uniform block,
				                                       uniform int64_t size,
				                                       uniform const char * uniform block_desc);

static uniform int memblock_alloc(uniform struct futhark_context * varying ctx,
				                          uniform struct memblock * varying block,
				                          varying int64_t size) {
  uniform int err = 0;

  foreach_active(i){
    err |= memblock_alloc((uniform struct futhark_context * uniform)(extract((varying int64_t)ctx,i)),
		   (uniform struct memblock * uniform)(extract((varying int64_t)block,i)),
		   extract(size, i),
		   &dummy_error);
  }

  return err;
}

static uniform int memblock_alloc(uniform struct futhark_context * uniform ctx,
				                          varying struct memblock * uniform block,
				                          uniform int64_t size) {
  uniform int err = 0;

  varying struct memblock _block = *block;
  uniform struct memblock aos[programCount];
  aos[programIndex] = _block;

  foreach_active(i){
    err |= memblock_alloc(ctx, &aos[i], size, &dummy_error);
  }
  *block = aos[programIndex];

  return err;
}

static uniform int memblock_alloc(uniform struct futhark_context * uniform ctx,
				                          varying struct memblock * uniform block,
				                          varying int64_t size) {
  uniform int err = 0;

  varying struct memblock _block = *block;
  uniform struct memblock aos[programCount];
  aos[programIndex] = _block;
  foreach_active(i){
    err |= memblock_alloc(ctx, &aos[i], extract(size, i), &dummy_error);
  }
  *block = aos[programIndex];

  return err;
}

extern "C" unmasked uniform int memblock_set(uniform struct futhark_context * uniform ctx,
                                             uniform struct memblock * uniform lhs,
                                             uniform struct memblock * uniform rhs,
                                             uniform const char * uniform lhs_desc);

static uniform int memblock_set (uniform struct futhark_context * uniform ctx,
                                 varying struct memblock * uniform lhs,
                                 varying struct memblock * uniform rhs) {
  uniform int err = 0;

  varying struct memblock _lhs = *lhs;
  varying struct memblock _rhs = *rhs;
  uniform struct memblock aos1[programCount];
  aos1[programIndex] = _lhs;

  uniform struct memblock aos2[programCount];
  aos2[programIndex] = _rhs;

  foreach_active(i) {
      err |= memblock_set(ctx,
      &aos1[i],
      &aos2[i],
      &dummy_error);
  }
  *lhs = aos1[programIndex];
  *rhs = aos2[programIndex];

  return err;
}

static uniform int memblock_set (uniform struct futhark_context * uniform ctx,
                                 varying struct memblock * uniform lhs,
                                 uniform struct memblock * uniform rhs) {
  uniform int err = 0;

  varying struct memblock _lhs = *lhs;
  uniform struct memblock aos1[programCount];
  aos1[programIndex] = _lhs;

  foreach_active(i) {
      err |= memblock_set(ctx,
      &aos1[i],
      rhs,
      &dummy_error);
  }
  *lhs = aos1[programIndex];

  return err;
}

// AOS <-> SOA methods

static inline varying uint8 * uniform uniformize_ptr(varying uint8 * varying ptr) {
    varying int64_t num = (varying int64_t)ptr;
    //uniform size_t res;
    //if (reduce_equal(num, &res)) {
        return (varying uint8 * uniform)extract(num, 0);
    //} else {
    //    return (varying uint8 * uniform)res;
    //}
    // TODO(pema): Is this safe?
}

// -----------------------------------------------------------------------------
static inline void memmove_1(varying uint8 * uniform dst, uniform uint8 * varying src, uniform int64_t n) {
    uniform uint8 * varying srcp = (uniform uint8 * varying) src;
    varying uint8 * uniform dstp = (varying uint8 * uniform) dst;
    for (uniform int i = 0; i < n / 1; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_1(uniform uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint8 * uniform srcp = (varying uint8 * uniform) src;
    uniform uint8 * varying dstp = (uniform uint8 * varying) dst;
    for (uniform int i = 0; i < n / 1; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_1(varying uint8 * uniform dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint8 * uniform srcp = (varying uint8 * uniform) src;
    varying uint8 * uniform dstp = (varying uint8 * uniform) dst;
    for (uniform int i = 0; i < n / 1; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_1(varying uint8 * varying dst, uniform uint8 * varying src, uniform int64_t n) {
    memmove_1(uniformize_ptr(dst), src, n);
}

static inline void memmove_1(uniform uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_1(dst, uniformize_ptr(src), n);
}

static inline void memmove_1(varying uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    memmove_1(uniformize_ptr(dst), src, n);
}

static inline void memmove_1(varying uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_1(uniformize_ptr(dst), uniformize_ptr(src), n);
}

// -----------------------------------------------------------------------------
static inline void memmove_2(varying uint8 * uniform dst, uniform uint8 * varying src, uniform int64_t n) {
    uniform uint16 * varying srcp = (uniform uint16 * varying) src;
    varying uint16 * uniform dstp = (varying uint16 * uniform) dst;
    for (uniform int i = 0; i < n / 2; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_2(uniform uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint16 * uniform srcp = (varying uint16 * uniform) src;
    uniform uint16 * varying dstp = (uniform uint16 * varying) dst;
    for (uniform int i = 0; i < n / 2; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_2(varying uint8 * uniform dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint16 * uniform srcp = (varying uint16 * uniform) src;
    varying uint16 * uniform dstp = (varying uint16 * uniform) dst;
    for (uniform int i = 0; i < n / 2; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_2(varying uint8 * varying dst, uniform uint8 * varying src, uniform int64_t n) {
    memmove_2(uniformize_ptr(dst), src, n);
}

static inline void memmove_2(uniform uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_2(dst, uniformize_ptr(src), n);
}

static inline void memmove_2(varying uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    memmove_2(uniformize_ptr(dst), src, n);
}

static inline void memmove_2(varying uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_2(uniformize_ptr(dst), uniformize_ptr(src), n);
}

// -----------------------------------------------------------------------------
static inline void memmove_4(varying uint8 * uniform dst, uniform uint8 * varying src, uniform int64_t n) {
    uniform uint32 * varying srcp = (uniform uint32 * varying) src;
    varying uint32 * uniform dstp = (varying uint32 * uniform) dst;
    for (uniform int i = 0; i < n / 4; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_4(uniform uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint32 * uniform srcp = (varying uint32 * uniform) src;
    uniform uint32 * varying dstp = (uniform uint32 * varying) dst;
    for (uniform int i = 0; i < n / 4; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_4(varying uint8 * uniform dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint32 * uniform srcp = (varying uint32 * uniform) src;
    varying uint32 * uniform dstp = (varying uint32 * uniform) dst;
    for (uniform int i = 0; i < n / 4; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_4(varying uint8 * varying dst, uniform uint8 * varying src, uniform int64_t n) {
    memmove_4(uniformize_ptr(dst), src, n);
}

static inline void memmove_4(uniform uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_4(dst, uniformize_ptr(src), n);
}

static inline void memmove_4(varying uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    memmove_4(uniformize_ptr(dst), src, n);
}

static inline void memmove_4(varying uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_4(uniformize_ptr(dst), uniformize_ptr(src), n);
}

// -----------------------------------------------------------------------------
static inline void memmove_8(varying uint8 * uniform dst, uniform uint8 * varying src, uniform int64_t n) {
    uniform uint64 * varying srcp = (uniform uint64 * varying) src;
    varying uint64 * uniform dstp = (varying uint64 * uniform) dst;
    for (uniform int i = 0; i < n / 8; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_8(uniform uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint64 * uniform srcp = (varying uint64 * uniform) src;
    uniform uint64 * varying dstp = (uniform uint64 * varying) dst;
    for (uniform int i = 0; i < n / 8; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_8(varying uint8 * uniform dst, varying uint8 * uniform src, uniform int64_t n) {
    varying uint64 * uniform srcp = (varying uint64 * uniform) src;
    varying uint64 * uniform dstp = (varying uint64 * uniform) dst;
    for (uniform int i = 0; i < n / 8; i++) {
        dstp[i] = srcp[i];
    }
}

static inline void memmove_8(varying uint8 * varying dst, uniform uint8 * varying src, uniform int64_t n) {
    memmove_8(uniformize_ptr(dst), src, n);
}

static inline void memmove_8(uniform uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_8(dst, uniformize_ptr(src), n);
}

static inline void memmove_8(varying uint8 * varying dst, varying uint8 * uniform src, uniform int64_t n) {
    memmove_8(uniformize_ptr(dst), src, n);
}

static inline void memmove_8(varying uint8 * varying dst, varying uint8 * varying src, uniform int64_t n) {
    memmove_8(uniformize_ptr(dst), uniformize_ptr(src), n);
}