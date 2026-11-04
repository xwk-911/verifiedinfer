#include "verifiedinfer/memory/token_buffer.h"
#include "support/check.h"

static void test_buffer_boundaries(void)
{
    vi_token storage[] = {91, 92, 93, 94};
    vi_token_buffer buffer;
    CHECK(vi_token_buffer_init(&buffer, storage + 1, 2) == VI_OK);
    CHECK(vi_token_buffer_append(&buffer, 7) == VI_OK);
    CHECK(vi_token_buffer_append(&buffer, UINT32_MAX) == VI_OK);
    CHECK(vi_token_buffer_append(&buffer, 8) == VI_NO_SPACE);
    CHECK(buffer.len == 2 && storage[1] == 7 && storage[2] == UINT32_MAX);
    CHECK(storage[0] == 91 && storage[3] == 94);
    CHECK(vi_token_buffer_init(&buffer, NULL, 0) == VI_OK);
    CHECK(vi_token_buffer_append(&buffer, 1) == VI_NO_SPACE);
    CHECK(vi_token_buffer_init(&buffer, storage, SIZE_MAX) == VI_INVALID);
    CHECK(buffer.data == NULL && buffer.len == 0 && buffer.capacity == 0);
    CHECK(vi_token_buffer_append(NULL, 1) == VI_INVALID);
}

int main(void)
{
    test_buffer_boundaries();
    puts("PASS: token buffer boundaries and failure preservation");
    return 0;
}
